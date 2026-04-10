use rustc_hash::FxHashMap;
use std::fs::File;
use std::os::unix::fs::FileExt;
use zerocopy::FromZeros;

use super::frame::FrameReadGuard;
use super::frame::FrameSlab;
use super::frame::FrameWriteGuard;
use super::pages::checksum;
use super::StorageError;
use super::PAGE_ID_NULL;
use crate::storage::PAGE_SIZE;
use crate::sync::*;

pub(super) struct Pager {
    file: File,
    framer: FrameSlab,
    /// All shards' maps of `page_id` -> `frame_index`
    shard_dirs: Box<[RwLock<PageBufferShard>]>,
    eviction_hand: AtomicUsize,
    poisoned: AtomicBool,
}

pub(super) struct PageBufferShard {
    // making this a struct incase we add more later - might flatten
    /// Shard's map of `page_id` -> `frame_index`
    dir: FxHashMap<u64, usize>,
}

impl Pager {
    // --------------------------------------------------------------------------------
    // *            constructor                                                       *
    // --------------------------------------------------------------------------------

    pub(super) fn new(frame_count: usize, file: File) -> Self {
        assert_ne!(frame_count, 0);

        let framer = FrameSlab::new(frame_count);

        let shard_dirs = (0..Self::SHARD_CNT)
            .map(|_| {
                let mut map = FxHashMap::default();
                map.reserve(frame_count / Self::SHARD_CNT);
                RwLock::new(PageBufferShard { dir: map })
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        Self { file, framer, shard_dirs, eviction_hand: AtomicUsize::new(0), poisoned: false.into() }
    }

    // --------------------------------------------------------------------------------
    // *            util                                                              *
    // --------------------------------------------------------------------------------

    const SHARD_CNT: usize = 64;

    const fn shard_hash(mut page_id: u64) -> usize {
        page_id ^= page_id >> 33;
        page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
        page_id ^= page_id >> 33;
        (page_id as usize) & (Self::SHARD_CNT - 1)
    }

    fn check_poisoned(&self) -> Result<(), StorageError> {
        if self.poisoned.load(Ordering::Acquire) {
            Err(StorageError::Poisoned)
        } else {
            Ok(())
        }
    }

    // --------------------------------------------------------------------------------
    // *            paging                                                            *
    // --------------------------------------------------------------------------------

    /// Gets, pins, and writelocks and unused frame
    /// Maybe evicts a frame
    /// **NOTE**: it may contain dirty data, and its fields will not be initialized correctly
    /// (page_id, dirty, is_err)**
    // **NOTE**: this will always give a frame in the Uninitialized state
    fn get_free_frame(&self) -> Result<FrameWriteGuard<'_>, StorageError> {
        self.check_poisoned()?;
        loop {
            let frame = &self.framer[self.scan_for_eviction_candidate()];
            let hinted_page_id = frame.page_id_hint.load(Ordering::Acquire);

            let dir_guard_opt = match hinted_page_id {
                PAGE_ID_NULL => None,
                _ => Some(self.shard_dirs[Self::shard_hash(hinted_page_id)].write().unwrap()),
            };
            let mut frame_guard = self.framer.pin_write(frame.index);

            if frame.pins.load(Ordering::Acquire) != 1 {
                // Someone else pinned this frame between our scan and now; try again.
                frame_guard.release();
                continue;
            }

            if let Some(actual_page_id) = frame_guard.has_page() {
                // If the hint was stale and pointed to the wrong shard, we can't safely remove
                // the directory entry — we'd be holding the wrong shard lock. Retry.
                match dir_guard_opt {
                    None => {
                        frame_guard.release();
                        continue;
                    }
                    Some(mut dir_guard) => {
                        if Self::shard_hash(hinted_page_id) != Self::shard_hash(actual_page_id) {
                            frame_guard.release();
                            continue;
                        }

                        // TODO we are currently holding the dir guard while writing
                        if frame_guard.is_dirty().is_some() {
                            self.io_write_out_frame(&mut frame_guard)?;
                        }

                        dir_guard.dir.remove(&actual_page_id);
                        frame.page_id_hint.store(PAGE_ID_NULL, Ordering::Release);
                    }
                }
            }

            frame_guard.state_to_uninit();
            return Ok(frame_guard);
        }
    }

    /// Scans for an eviction candidate (frame with 0 pins and 0 usage). This will spin until
    /// one is found. It is imperative that the caller re-check these conditions once a lock on the
    /// shard directory has been acquired, so we dont TOCTOU.
    fn scan_for_eviction_candidate(&self) -> usize {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            let frame_index = self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.framer.frame_count();
            let frame = &self.framer[frame_index];

            if frame.pins.load(Ordering::Acquire) == 0 {
                // This could be Relaxed but it might result in more aborts once we take the lock
                // later? Would need testing really. Either is "correct" because we recheck later.

                let usage = loop {
                    // theres no atomic saturating sub so we have to do a little dance, otherwise we
                    // can have a TOCTOU where two threads decrement this usage and it wraps
                    let fetched_usage = frame.usage.load(Ordering::Relaxed);

                    if fetched_usage == 0 {
                        break 0;
                    }

                    let res = frame.usage.compare_exchange(
                        fetched_usage,
                        fetched_usage - 1,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    );

                    if res.is_ok() {
                        break fetched_usage;
                    }
                };

                if usage == 0 {
                    return frame_index;
                }
            }

            checked_count += 1;
            if checked_count == self.framer.frame_count() {
                // hint that were spinning if weve looked through all the frames already
                std::hint::spin_loop();
                checked_count = 0;
            }
        }
    }

    /// Fetches existing page
    pub(super) fn get_page_existing(&self, page_id: u64) -> Result<FrameReadGuard<'_>, StorageError> {
        let shard = Self::shard_hash(page_id);

        // if its already paged in
        let shard_guard = self.shard_dirs[shard].read().unwrap();
        if let Some(&frame_index) = shard_guard.dir.get(&page_id) {
            return Ok(self.framer.pin_read(frame_index));
        }
        drop(shard_guard);

        // we need to page it in and load it

        // this puts it in the dir right away, which is useful because other threads can see we
        // already have inflight io
        let mut frame_guard = self.get_free_frame()?;

        // we now need to make entry for this page in directory
        let mut dir_guard = self.shard_dirs[shard].write().unwrap();

        // check if another thread beat us to populating this page_id in the dir
        // well abandon our frame and use theres instead
        if let Some(&found_frame_index) = dir_guard.dir.get(&page_id) {
            // we need to set our frame to uninit, to make sure another frame doesnt later choose
            // it for eviction, see its page_id, then remove that page_id from the dir
            // (the page_id is the same as the actual frame that were going to take!)
            frame_guard.cancel();

            let frame_guard = self.framer.pin_read(found_frame_index);
            // if the frame we adopt has an error we just return that error - no retry
            if let Some(err) = frame_guard.has_read_error() {
                return Err(err);
            }

            return Ok(frame_guard);
        }

        dir_guard.dir.insert(page_id, frame_guard.index);
        self.framer[frame_guard.index]
            .page_id_hint
            .store(page_id, Ordering::Release);
        drop(dir_guard);

        // fetch data
        frame_guard.state_uninit_to_readpending(page_id);
        let res = self.io_read_into_frame(&mut frame_guard);

        match res {
            Ok(()) => {
                let index = frame_guard.index;
                frame_guard.release(); // this is where we used to have a downgrade
                let frame_guard = self.framer.pin_read(index);
                Ok(frame_guard)
            }
            Err(err) => {
                let frame_index = frame_guard.index;
                // Remove from dir and clear hint before releasing the frame
                let mut shard_guard = self.shard_dirs[shard].write().unwrap();
                shard_guard.dir.remove(&page_id);
                self.framer[frame_index]
                    .page_id_hint
                    .store(PAGE_ID_NULL, Ordering::Release);
                drop(shard_guard);
                frame_guard.cancel();
                Err(err)
            }
        }
    }

    /// Gives an empty frame with a new page. Its `page_id`, `dirty` flag and `io_err` will be reset.
    /// The page will be zeroed.
    ///
    /// **NOTE**: It is assumed that, for a given `page_id`, `get_page_new` will only ever be called
    /// once. Multiple threads calling this with the same `page_id` will result in a race.
    pub(super) fn get_page_new(&self, new_page_id: u64) -> Result<FrameWriteGuard<'_>, StorageError> {
        let mut frame_guard = self.get_free_frame()?;

        frame_guard.buffer.zero();
        frame_guard.state_uninit_to_writeable(new_page_id);

        let mut dir_guard = self.shard_dirs[Self::shard_hash(new_page_id)].write().unwrap();
        debug_assert!(!dir_guard.dir.contains_key(&new_page_id), "page was already in directory");
        dir_guard.dir.insert(new_page_id, frame_guard.index);

        self.framer[frame_guard.index]
            .page_id_hint
            .store(new_page_id, Ordering::Release);

        Ok(frame_guard)
    }

    // --------------------------------------------------------------------------------
    // *            io                                                                *
    // --------------------------------------------------------------------------------

    fn io_read_into_frame(&self, frame_guard: &mut FrameWriteGuard<'_>) -> Result<(), StorageError> {
        let page_id = frame_guard.has_page().expect("frame in wrong state");
        let mut result = self
            .file
            .read_exact_at(frame_guard.buffer, PAGE_SIZE as u64 * page_id)
            .map_err(|err| err.kind().into());

        if let Err(err) = result {
            log::error!("read error (page_id={}): {}", page_id, err);
        } else if !checksum::check(frame_guard.buffer) {
            log::error!("read checksum error (page_id={})", page_id);
            result = Err(StorageError::Checksum); // TODO error type
        }

        frame_guard.state_readpending_to_read(result.err());
        result
    }

    fn io_write_out_frame(&self, frame_guard: &mut FrameWriteGuard<'_>) -> Result<(), StorageError> {
        let page_id = frame_guard.is_dirty().expect("frame in wrong state (should be dirty)");
        checksum::set(frame_guard.buffer);

        let result = self
            .file
            .write_all_at(frame_guard.buffer, PAGE_SIZE as u64 * page_id)
            .map_err(|err| err.kind().into());

        if let Err(err) = result {
            log::error!("write error (page_id={}): {}", page_id, err);
            self.poisoned.store(true, Ordering::Release);
            std::process::abort();
        }

        frame_guard.state_dirty_to_writtenout();
        result
    }
}
