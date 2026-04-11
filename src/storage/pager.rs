use rustc_hash::FxHashMap;
use std::fs::File;
use std::os::unix::fs::FileExt;
use zerocopy::FromZeros;

use super::frame::*;
use super::pages::checksum;
use super::StorageError;
use super::PAGE_ID_NULL;
use crate::storage::PAGE_SIZE;
use crate::sync::*;

pub(super) struct Pager {
    file: File,
    framer: FrameSlab,
    /// All shards' maps of `page_id` -> `frame_index`
    shard_dirs: Box<[RwLock<FxHashMap<u64, usize>>]>,
    eviction_hand: AtomicUsize,
    poisoned: AtomicBool,
}

impl Pager {
    // ---------------------------------------------------------------------------------------------
    // *            CONSTRUCTOR                                                                    *
    // ---------------------------------------------------------------------------------------------

    pub(super) fn new(frame_count: usize, file: File) -> Self {
        assert!(frame_count > 0);
        let framer = FrameSlab::new(frame_count);

        let shard_dirs = (0..Self::SHARD_CNT)
            .map(|_| {
                let mut map = FxHashMap::default();
                map.reserve(frame_count / Self::SHARD_CNT);
                RwLock::new(map)
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        Self {
            file,
            framer,
            shard_dirs,
            eviction_hand: AtomicUsize::new(0),
            poisoned: false.into(),
        }
    }

    // ---------------------------------------------------------------------------------------------
    // *            UTIL                                                                           *
    // ---------------------------------------------------------------------------------------------

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

    // ---------------------------------------------------------------------------------------------
    // *            PAGING                                                                         *
    // ---------------------------------------------------------------------------------------------

    /// Fetches existing page
    /// **NOTE**: this will always give a frame in the ReadSuccessful state (in the event of an error
    /// Err will be returned, but the frame will exist as ReadErrored)
    #[must_use = "RAII FrameGuard releases when dropped"]
    pub(super) fn get_page_existing(
        &self, target_page_id: u64,
    ) -> Result<FrameReadGuard<'_, Readable>, StorageError> {
        let shard_idx = Self::shard_hash(target_page_id);

        // if its already paged in
        let dir_guard = self.shard_dirs[shard_idx].read().unwrap();

        if let Some(&frame_idx) = dir_guard.get(&target_page_id) {
            if let Ok(guard) = self.framer.pin_read(frame_idx) {
                return Ok(guard);
            }
        }
        drop(dir_guard);

        // **IO path**: we need to page it in and load it
        // ----------------------------------------------

        // this puts it in the dir right away, which is useful because other threads can see we
        // already have inflight io
        let frame_guard = self.get_free_frame()?;
        let mut dir_guard = self.shard_dirs[shard_idx].write().unwrap();

        // we now need to make entry for this page in directory
        //
        // check if another thread beat us to populating this page_id in the dir
        // well abandon our frame and use theirs instead
        if let Some(&found_frame_idx) = dir_guard.get(&target_page_id) {
            // we need to set our frame to uninit, to make sure another frame doesnt later choose it
            // for eviction, see its page_id, then remove that page_id from the dir (the page_id is
            // the same as the actual frame that were going to take!)
            frame_guard.abandon();

            // in this case we could retry ourselves, but for now we will just return the error TODO
            return self.framer.pin_read(found_frame_idx);
        }

        // set to pending, insert into dir
        let frame_guard = frame_guard.mark_load_pending(target_page_id);

        // eprintln!("t{}: inserting exist {}...", thread_id(), target_page_id);
        dir_guard.insert(target_page_id, frame_guard.index);
        self.framer[frame_guard.index].page_id_hint.store(target_page_id, Ordering::Release);
        drop(dir_guard);

        // fetch data
        let frame_idx = frame_guard.index;
        let res = self.io_read_into_frame(frame_guard);

        match res {
            Ok(frame_guard) => Ok(frame_guard),
            Err(err) => {
                // Remove from dir and clear hint before releasing the frame
                {
                    let mut dir_guard = self.shard_dirs[shard_idx].write().unwrap();
                    dir_guard.remove(&target_page_id);
                    self.framer[frame_idx].page_id_hint.store(PAGE_ID_NULL, Ordering::Release);
                }
                Err(err)
            }
        }
    }

    /// This has some optimizations that rely on the assumption that we will under no circumstances
    /// find the page_id already resident in the pager. This method is **NOT** correct if this is
    /// the case. ASSERTS page_id will not be found in pager
    /// Gives an empty frame with a new page. Its `page_id`, `dirty` flag and `io_err` will be
    /// reset. The page will be zeroed.
    #[must_use = "RAII FrameGuard releases when dropped"]
    pub(super) fn get_page_new(
        &self, target_page_id: u64,
    ) -> Result<FrameWriteGuard<'_, Writeable>, StorageError> {
        let mut frame_guard = self.get_free_frame()?;

        // initialize frame
        frame_guard.buffer().zero();
        let frame_guard = frame_guard.mark_writeable(target_page_id);

        // put it into the dir
        let mut dir_guard = self.shard_dirs[Self::shard_hash(target_page_id)].write().unwrap();

        let prev = dir_guard.insert(target_page_id, frame_guard.index);
        assert!(
            prev.is_none(),
            "page was already in directory - by calling get_page_new you are asserting that \
            we will not find this page_id in the pager, even AFTER we call get_free_frame"
        );

        // set hint
        self.framer[frame_guard.index].page_id_hint.store(target_page_id, Ordering::Release);
        Ok(frame_guard)
    }

    /// Gets, pins, and writelocks and unused frame. Maybe evicts a frame
    /// **NOTE**: it may contain dirty data, and its fields will not be initialized correctly
    /// (page_id, dirty, is_err)**
    // **NOTE**: this will always give a frame in the Uninitialized state
    #[must_use = "RAII FrameGuard releases when dropped"]
    fn get_free_frame(&self) -> Result<FrameWriteGuard<'_, Uninit>, StorageError> {
        self.check_poisoned()?;
        loop {
            let frame = &self.framer[self.scan_for_eviction_candidate()];
            let hinted_page_id = frame.page_id_hint.load(Ordering::Acquire);

            let dir_guard_opt = match hinted_page_id {
                PAGE_ID_NULL => None,
                _ => Some(self.shard_dirs[Self::shard_hash(hinted_page_id)].write().unwrap()),
            };

            let Some(pin_res) = self.framer.pin_write_cas(frame.index) else {
                continue;
            };

            match pin_res {
                // we got an uninit frame - this should not be in our directory
                // we can simply hand it out
                PinWrite::Uninit(frame_guard) => {
                    return Ok(frame_guard);
                }

                // in both the Dirty and Resident case, if we are holding the wrong shard lock we
                // are just going to start over, because wed have to drop it and reacquire it, and
                // to prevent deadlocks we don't want to take locks in the dir -> frame order.
                // Note: the page_id != hinted_page_id check is CORRECT even if we read "NULL" as
                // the hint - because the frame is probably only NOW in a dir if it only NOW has a
                // page_id
                //
                PinWrite::ResidentDirty(frame_guard) => {
                    // we got a dirty frame - we have to write it out
                    match dir_guard_opt {
                        None => {
                            // Assumption: If we read pageahint:null but this frame is resident,
                            // someone put it into the dir SINCE we read the hint.
                            // -> retry
                            frame_guard.abandon();
                            continue;
                        }
                        Some(mut dir_guard) => {
                            let page_id = frame_guard.page_id();
                            if Self::shard_hash(page_id) != Self::shard_hash(hinted_page_id) {
                                // we are not holding the right dir
                                // -> retry
                                frame_guard.abandon();
                                continue;
                            }

                            // we can remove it from the dir now, then do our write-out. We hold a
                            // exclusive anyway.
                            // eprintln!("t{}: evicting dirty {}...", thread_id(), page_id);
                            dir_guard.remove(&page_id).expect(
                                "Either we checked wrong shard \
                                or someone didn't put frame into dir?",
                            );

                            let frame_guard = self.io_write_out_frame(frame_guard)?;
                            frame.page_id_hint.store(PAGE_ID_NULL, Ordering::Release);
                            return Ok(frame_guard);
                        }
                    }
                }

                PinWrite::ResidentReadable(frame_guard) => {
                    match dir_guard_opt {
                        None => {
                            // Assumption: If we read pageahint:null but this frame is resident,
                            // someone put it into the dir SINCE we read the hint.
                            // -> retry
                            frame_guard.abandon();
                            continue;
                        }
                        Some(mut dir_guard) => {
                            let page_id = frame_guard.page_id();
                            if Self::shard_hash(page_id) != Self::shard_hash(hinted_page_id) {
                                // we are not holding the right dir
                                // -> retry
                                frame_guard.abandon();
                                continue;
                            }

                            // otherwise just remove it from the dir and hand out the frame
                            dir_guard.remove(&page_id).expect(
                                "Either we checked wrong shard \
                                or someone didn't put frame into dir?",
                            );

                            frame.page_id_hint.store(PAGE_ID_NULL, Ordering::Release);
                            return Ok(frame_guard.mark_evicted());
                        }
                    }
                }
            }
        }
    }

    /// Scans for an eviction candidate (frame with 0 pins and 0 usage). This will spin until one is
    /// found. It is imperative that the caller re-check these conditions once a lock on the shard
    /// directory has been acquired, so we dont TOCTOU.
    fn scan_for_eviction_candidate(&self) -> usize {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            let frame_idx =
                self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.framer.frame_count();
            let frame = &self.framer[frame_idx];

            // This could be Relaxed (maybe) but it might result in more aborts once we take the
            // lock later? Would need testing really. Either is "correct" because we recheck later.
            if frame.pins.load(Ordering::Acquire) == 0 {
                let frame_usage_ctr = frame
                    .usage
                    .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |old| {
                        Some(old.saturating_sub(1))
                    })
                    .unwrap();

                if frame_usage_ctr == 0 {
                    return frame_idx;
                }
            }

            thread::yield_now();
            checked_count += 1;
            if checked_count == self.framer.frame_count() {
                // hint that were spinning if weve looked through all the frames already
                std::hint::spin_loop();
                checked_count = 0;
            }
        }
    }

    // --------------------------------------------------------------------------------------------
    // *            IO                                                                            *
    // --------------------------------------------------------------------------------------------

    fn io_read_into_frame<'a>(
        &self, mut frame_guard: FrameWriteGuard<'a, LoadPending>,
    ) -> Result<FrameReadGuard<'a, Readable>, StorageError> {
        let page_id = frame_guard.page_id();
        let mut result = self
            .file
            .read_exact_at(frame_guard.buffer(), PAGE_SIZE as u64 * page_id)
            .map_err(|err| err.kind().into());

        if let Err(err) = result {
            log::error!("read error (page_id={}): {}", page_id, err);
        } else if !checksum::check(frame_guard.buffer()) {
            log::error!("read checksum error (page_id={})", page_id);
            result = Err(StorageError::Checksum);
        }

        match result {
            Ok(()) => Ok(frame_guard.mark_load_ok()),
            Err(err) => {
                frame_guard.mark_load_err(err);
                return Err(err);
            }
        }
    }

    fn io_write_out_frame<'a>(
        &self, mut frame_guard: FrameWriteGuard<'a, Dirty>,
    ) -> Result<FrameWriteGuard<'a, Uninit>, StorageError> {
        let page_id = frame_guard.page_id();
        checksum::set(frame_guard.buffer());

        let result: Result<_, StorageError> = self
            .file
            .write_all_at(frame_guard.buffer(), PAGE_SIZE as u64 * page_id)
            .map_err(|err| err.kind().into());

        if let Err(err) = result {
            log::error!("write error (page_id={}): {}", page_id, err);
            self.poisoned.store(true, Ordering::Release);
            frame_guard.mark_poisoned();
            std::process::abort();
        }

        Ok(frame_guard.mark_written_out_and_reinit())
    }
}

// TODO delete
// CURRENT BUG:
// we request `get_page_new` on same page_id multiple times,
// we find free frames (just uninit) so we dont even look in the dir_guard
// we just put that shit in

// `get_page_new_1` handles all general cases where we want to write to a given arbitrary `page_id`.
// It should work even if the page is currently resident in the pager and even if the page is
// currently RW locked. We'll have to revise the Frame state machine rules to support this, as
// originally wed planned to oinly give out "Writeable" initialized frames but now well be
// possibly giving out frames that are `Dirty` or read-in from disk (`Readable`)

// `get_page_new_2` will only be correct if we are writing to a page that would notionally be
// "freed". What this means wrt the pager is that the page should NOT be resident - unlike
// `get_new_page_1` this should "fail" (in some way) if we pass in a `page_id` that is currently
// resident in the pager.
