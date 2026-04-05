use std::{
    cell::{Cell, RefCell},
    sync::{
        Arc,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
};

use parking_lot::RwLock;
use rustc_hash::FxHashMap;

use crate::{
    io,
    storage::{
        frame::{Frame, FrameRef, FrameWriteGuard},
        memory_alloc::MmapBox,
    },
};

thread_local! {
    static THREAD_IO: RefCell<Option<Box<dyn crate::io::IODoer>>> = RefCell::new(None);
}

static THREAD_TOKEN_PREFIX_NEXT: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static THREAD_TOKEN_PREFIX: u64 = THREAD_TOKEN_PREFIX_NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    static THREAD_TOKEN_NEXT: Cell<u64> = Cell::new(0);
}

fn next_thread_token() -> u64 {
    THREAD_TOKEN_PREFIX.with(|&token_prefix| {
        debug_assert!(token_prefix < 0x100, "Only 8 bits allocated for thread token prefix id (max 256 threads)");
        THREAD_TOKEN_NEXT.with(|token_next_cell| {
            let token_next = token_next_cell.get();
            token_next_cell.set(token_next + 1);
            (token_prefix << 56) | (token_next & 0x00ff_ffff_ffff_ffff)
        })
    })
}
const SHARD_CNT: usize = 64;
fn hash(mut page_id: u64) -> usize {
    page_id ^= page_id >> 33;
    page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
    page_id ^= page_id >> 33;
    (page_id as usize) & (SHARD_CNT - 1)
}

//  ▄▄▄· ▄▄▄·  ▄▄ • ▄▄▄ .    ▄▄▄▄· ▄• ▄▌·▄▄▄·▄▄▄▄▄▄ .▄▄▄
// ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪▀▄.▀·    ▐█ ▀█▪█▪██▌▐▄▄·▐▄▄·▀▄.▀·▀▄ █·
//  ██▀·▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄    ▐█▀▀█▄█▌▐█▌██▪ ██▪ ▐▀▀▪▄▐▀▀▄
// ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌    ██▄▪▐█▐█▄█▌██▌.██▌.▐█▄▄▌▐█•█▌
// .▀    ▀  ▀ ·▀▀▀▀  ▀▀▀     ·▀▀▀▀  ▀▀▀ ▀▀▀ ▀▀▀  ▀▀▀ .▀  ▀
// Page Buffer

type PageId = u64;

pub(super) struct PageBuffer {
    pub(super) io: Arc<dyn crate::io::IOFactory>,
    frames: MmapBox<[Frame]>,
    /// All shards' maps of `page_id` -> `frame_index`
    shard_dirs: Box<[RwLock<PageBufferShard>]>,
    eviction_hand: AtomicUsize,
}

pub(super) struct PageBufferShard {
    // making this a struct incase we add more later - might flatten
    /// Shard's map of `page_id` -> `frame_index`
    dir: FxHashMap<PageId, usize>,
}

impl PageBuffer {
    pub(super) fn new(io: Arc<dyn crate::io::IOFactory>, frame_count: usize) -> Self {
        assert_ne!(frame_count, 0);

        let mut i = 0;
        let (frames, allocated_bytes) = MmapBox::<[Frame]>::new_slice_with(frame_count, || {
            let frame = Frame::new(i);
            i += 1;
            frame
        });

        tracing::info!("PageBuffer reserved {}", monke::fmt_size(allocated_bytes));

        let shard_dirs = Vec::from_iter((0..SHARD_CNT).into_iter().map(|_| {
            let mut map = FxHashMap::default();
            map.reserve(frame_count / SHARD_CNT);
            RwLock::new(PageBufferShard { dir: map })
        }))
        .into_boxed_slice();

        Self { io, frames, shard_dirs, eviction_hand: AtomicUsize::new(0) }
    }

    //  ▄▄▄· ▄▄▄·  ▄▄ • ▪   ▐ ▄  ▄▄ •
    // ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪██ •█▌▐█▐█ ▀ ▪
    //  ██▀·▄█▀▀█ ▄█ ▀█▄▐█·▐█▐▐▌▄█ ▀█▄
    // ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▌██▐█▌▐█▄▪▐█
    // .▀    ▀  ▀ ·▀▀▀▀ ▀▀▀▀▀ █▪·▀▀▀▀
    //  Paging & Eviction

    /// Gives an empty frame with a new page. Its `page_id`, `dirty` flag and `io_err` will be reset,
    /// however its `buffer` can contain old garbage.
    ///
    /// **NOTE**: It is assumed that, for a given `page_id`, `get_page_new` will only ever be called
    /// once. Multiple threads calling this with the same `page_id` will result in a race.
    pub(super) fn get_page_new(
        &self, new_page_id: u64,
    ) -> Result<(FrameRef<'_>, FrameWriteGuard<'_>), std::io::ErrorKind> {
        let (frame_ref, mut frame_guard) = match self.get_free_frame() {
            Err(err) => return Err(err),
            Ok(ret) => ret,
        };

        frame_guard.reinit(new_page_id);

        let mut dir_guard = self.shard_dirs[hash(frame_guard.page_id)].write();
        debug_assert!(dir_guard.dir.get(&frame_guard.page_id).is_none(), "page was already in directory");
        dir_guard.dir.insert(frame_guard.page_id, frame_ref.index());

        Ok((frame_ref, frame_guard))
    }

    /// Fetches existing page
    pub(super) fn get_page_existing(&self, page_id: u64) -> Result<FrameRef<'_>, std::io::ErrorKind> {
        let shard = hash(page_id);

        // if its already paged in
        let shard_guard = self.shard_dirs[shard].read();
        if let Some(&frame_index) = shard_guard.dir.get(&page_id) {
            return Ok(self.frames[frame_index].pin());
        }
        drop(shard_guard);

        // we need to page it in and load it

        // this puts it in the dir right away, which is useful because other threads can see we
        // already have inflight io
        let (frame_ref, mut frame_guard) = {
            match self.get_free_frame() {
                Err(err) => return Err(err),
                Ok(ret) => ret,
            }
        };

        frame_guard.reinit(page_id);

        // we now need to make entry for this page in directory
        let mut dir_guard = self.shard_dirs[shard].write();

        // check if another thread beat us to populating this page_id in the dir
        // well abandon our frame and use theres instead
        if let Some(&found_frame_index) = dir_guard.dir.get(&frame_guard.page_id) {
            // we need to set our frame to uninit, to make sure another frame doesnt later choose
            // it for eviction, see its page_id, then remove that page_id from the dir
            // (the page_id is the same as the actual frame that were going to take!)
            frame_guard.uninit();
            drop(frame_guard);

            let frame_ref = self.frames[found_frame_index].pin();
            // if the frame we adopt has an error we just return that error - no retry
            if let Some(err) = frame_ref.read_lock().io_err.clone() {
                return Err(err);
            }

            return Ok(frame_ref);
        }
        dir_guard.dir.insert(frame_guard.page_id, frame_ref.index());
        drop(dir_guard);

        // fetch data
        let res = self.io_read_one(&mut frame_guard);
        match res {
            Ok(()) => Ok(frame_ref),
            Err(err) => {
                // if err well remove and set err on frame
                self.shard_dirs[shard].write().dir.remove(&page_id);
                frame_guard.io_err = Some(err.clone());
                Err(err)
            }
        }
    }

    /// Gets, pins, and writelocks and unused frame
    /// Maybe evicts a frame
    /// **NOTE: it may contain dirty data, and its fields will not be initialized correctly
    /// (page_id, dirty, is_err)**
    fn get_free_frame(&self) -> Result<(FrameRef<'_>, FrameWriteGuard<'_>), std::io::ErrorKind> {
        loop {
            let frame_index = self.scan_for_eviction_candidate();
            let frame_ref = self.frames[frame_index].pin();

            // we'll optimistically try to get a lock on this frame - if we dont, then someone else
            // evicted this frame before we got a chance, so well try again and find another one
            if let Some(mut frame_guard) = frame_ref.try_write_lock() {
                if frame_guard.has_non_init_page() {
                    let mut dir_guard = self.shard_dirs[hash(frame_guard.page_id)].write();

                    if frame_ref.pins.load(Ordering::Acquire) != 1 {
                        // we need to recheck pins again after we take the old directory lock, to make
                        // sure nobody found this and pinned it in the meantime
                        // If someone did we drop all our locks and start over
                        continue;
                    }

                    dir_guard.dir.remove(&frame_guard.page_id);
                    drop(dir_guard);

                    if frame_guard.dirty {
                        if let Err(err) = self.io_write_one(&frame_guard) {
                            return Err(err);
                        }
                        frame_guard.dirty = false;
                    }
                }

                return Ok((frame_ref, frame_guard));
            }
        }
    }

    /// Scans for an eviction candidate (frame with 0 pins and 0 usage). This will spin until
    /// one is found. It is imperative that the caller re-check these conditions once a lock on the
    /// shard directory has been acquired, so we dont TOCTOU.
    fn scan_for_eviction_candidate(&self) -> usize {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            let frame_index = self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.frames.len();
            let frame = &self.frames[frame_index];

            if frame.pins.load(Ordering::Acquire) == 0 {
                // This could be Relaxed but it might result in more aborts once we take the lock
                // later? Would need testing really. Either is "correct" because we recheck later.

                let usage = loop {
                    // theres no atomic saturating sub so we have to do a little dance, otherwise we
                    // can have a TOCTOU where two threads decrement this usage and it wraps
                    let fetched_usage = frame.usage.load(Ordering::Relaxed);
                    if fetched_usage == 0 {
                        break 0;
                    } else {
                        let res = frame.usage.compare_exchange(
                            fetched_usage,
                            fetched_usage - 1,
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        );

                        if res.is_ok() {
                            break fetched_usage;
                        }
                    }
                };

                if usage == 0 {
                    return frame_index;
                }
            }

            checked_count += 1;
            if checked_count == self.frames.len() {
                // hint that were spinning if weve looked through all the frames already
                std::hint::spin_loop();
                checked_count = 0;
            }
        }
    }

    // ▪
    // ██ ▪
    // ▐█· ▄█▀▄
    // ▐█▌▐█▌.▐▌
    // ▀▀▀ ▀█▄▀▪
    // IO

    /// Must be called once by each worker thread before using the buffer.
    pub(super) fn init_thread(&self) {
        THREAD_IO.with(|cell| {
            assert!(cell.borrow().is_none(), "Tried to init thread-io twice!");
            *cell.borrow_mut() = Some(self.io.make_io_doer())
        });
    }

    pub(super) fn thread_io<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&dyn io::IODoer) -> R,
    {
        THREAD_IO.with(|cell| f(cell.borrow().as_deref().expect("init_thread not called")))
    }

    fn io_read_one(&self, frame_guard: &mut FrameWriteGuard<'_>) -> Result<(), std::io::ErrorKind> {
        self.thread_io(|io| {
            debug_assert_eq!(io.peek(), 0, "queue was dirty before we submitted anything?");
            let token = next_thread_token();
            unsafe { io.submit_read(token, frame_guard.page_id, &mut frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token, "received a token other than the one we submitted - queue was dirty?");
            res
        })
    }

    fn io_write_one(&self, frame_guard: &FrameWriteGuard<'_>) -> Result<(), std::io::ErrorKind> {
        self.thread_io(|io| {
            debug_assert_eq!(io.peek(), 0, "queue was dirty before we submitted anything?");
            let token = next_thread_token();
            unsafe { io.submit_write(token, frame_guard.page_id, &frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token, "received a token other than the one we submitted - queue was dirty?");
            res
        })
    }

    // TODO flush all
}

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::{io::mem_io::MemIO, page::PAGE_SIZE};

    fn make_buf(frame_count: usize) -> PageBuffer {
        let buf = PageBuffer::new(Arc::new(MemIO::new()), frame_count);
        buf.init_thread();
        buf
    }

    // ─── get_page_new ───────────────────────────────────────────────────────────

    #[test]
    fn get_page_new_sets_page_id() {
        let buf = make_buf(4);

        let (_r, g) = buf.get_page_new(42).expect("should allocate frame");

        assert_eq!(g.page_id, 42);
    }

    #[test]
    fn get_page_new_clears_dirty_and_io_err() {
        let buf = make_buf(4);

        let (_r, g) = buf.get_page_new(1).expect("should allocate frame");

        assert!(!g.dirty, "dirty must be false after get_page_new");
        assert!(g.io_err.is_none(), "io_err must be None after get_page_new");
    }

    #[test]
    fn get_page_new_different_ids_get_different_frames() {
        let buf = make_buf(4);

        let (r1, _g1) = buf.get_page_new(1).expect("page 1");
        let (r2, _g2) = buf.get_page_new(2).expect("page 2");
        let (r3, _g3) = buf.get_page_new(3).expect("page 3");

        assert_ne!(r1.index(), r2.index());
        assert_ne!(r2.index(), r3.index());
        assert_ne!(r1.index(), r3.index());
    }

    // ─── get_page_existing ──────────────────────────────────────────────────────

    #[test]
    fn get_page_existing_finds_cached_page_in_same_frame() {
        let buf = make_buf(4);

        let (orig_ref, g) = buf.get_page_new(7).expect("allocate page 7");
        let orig_index = orig_ref.index();
        drop(g);
        // keep orig_ref alive so the frame stays pinned and cannot be evicted

        let found = buf.get_page_existing(7).expect("should find page 7 in buffer");

        assert_eq!(found.index(), orig_index, "get_page_existing must return the same frame as get_page_new");
    }

    // ─── eviction & dirty flush ─────────────────────────────────────────────────

    /// Fill all 3 frames, mark one dirty, force it out by requesting a 4th page,
    /// then reload that page from IO and verify the data survived the eviction cycle.
    #[test]
    fn dirty_page_data_survives_eviction_and_reload() {
        let buf = make_buf(3);
        let pattern = [0xABu8; PAGE_SIZE];

        // Allocate all 3 frames.
        let (r1, mut g1) = buf.get_page_new(1).expect("page 1");
        let (r2, g2) = buf.get_page_new(2).expect("page 2");
        let (r3, g3) = buf.get_page_new(3).expect("page 3");

        // Write a recognizable pattern to page 1 and mark it dirty.
        g1.buffer.copy_from_slice(&pattern);
        g1.dirty = true;
        drop(g1);
        drop(r1); // unpin; frame for page 1 is the only eviction candidate

        // Request page 4: forces eviction of the only unpinned frame (page 1).
        // Because it was dirty, the eviction path must flush it to IO.
        let (r4, g4) = buf.get_page_new(4).expect("should evict dirty page 1");
        drop(g4);
        drop(r4);

        // Unpin pages 2 and 3 so their frames are free for the reload.
        drop(g2);
        drop(r2);
        drop(g3);
        drop(r3);

        // Re-fetch page 1; it must now be loaded back from IO with the original data.
        let reloaded = buf.get_page_existing(1).expect("should reload page 1 from IO");
        let guard = reloaded.read_lock();

        assert_eq!(guard.buffer, pattern, "reloaded buffer must match data written before eviction");
    }

    /// Same setup but the frame is NOT marked dirty; the buffer content must
    /// not be persisted, and a subsequent reload should return zeroes.
    #[test]
    fn clean_page_not_flushed_to_io_on_eviction() {
        let buf = make_buf(3);
        let garbage = [0xFFu8; PAGE_SIZE];

        let (r1, mut g1) = buf.get_page_new(1).expect("page 1");
        let (r2, g2) = buf.get_page_new(2).expect("page 2");
        let (r3, g3) = buf.get_page_new(3).expect("page 3");

        // Write to the frame buffer but do NOT set dirty.
        g1.buffer.copy_from_slice(&garbage);
        // g1.dirty remains false
        drop(g1);
        drop(r1);

        // Evict page 1 cleanly (no IO write should occur).
        let (r4, g4) = buf.get_page_new(4).expect("should evict clean page 1");
        drop(g4);
        drop(r4);
        drop(g2);
        drop(r2);
        drop(g3);
        drop(r3);

        // Reload page 1; MemIO returns zeroes for pages it has never written.
        let reloaded = buf.get_page_existing(1).expect("reload page 1");
        let guard = reloaded.read_lock();

        assert_eq!(guard.buffer, [0u8; PAGE_SIZE], "non-dirty eviction must not persist the frame contents");
    }

    // ─── pin protection ─────────────────────────────────────────────────────────

    /// A pinned frame must never be chosen as an eviction candidate.
    /// Allocate 2 frames, keep one pinned, request a third — the buffer must
    /// evict the unpinned frame and leave the pinned page intact.
    #[test]
    fn pinned_frame_is_not_evicted() {
        let buf = make_buf(2);

        let (r1, g1) = buf.get_page_new(1).expect("page 1");
        let (r2, g2) = buf.get_page_new(2).expect("page 2");

        // Unpin page 2 but keep page 1 fully pinned.
        drop(g2);
        drop(r2);

        // Requesting page 3 must evict page 2 (the only unpinned frame).
        let (_r3, g3) = buf.get_page_new(3).expect("should evict page 2 not page 1");
        assert_eq!(g3.page_id, 3);
        drop(g3);

        // Page 1 must still be resident in its original frame.
        let found = buf.get_page_existing(1).expect("page 1 must still be in buffer");
        assert_eq!(found.index(), r1.index(), "page 1 must still occupy its original frame");

        drop(g1);
        drop(r1);
    }

    // ─── concurrency ────────────────────────────────────────────────────────────

    /// Two threads calling get_page_existing for the same already-cached page
    /// must both succeed and see the correct page_id — no race, no deadlock.
    #[test]
    fn concurrent_get_page_existing_cached_page_both_succeed() {
        let buf = PageBuffer::new(Arc::new(MemIO::new()), 16);
        buf.init_thread();

        // Seed page 42 so it is in the directory.
        let (r, g) = buf.get_page_new(42).expect("seed page 42");
        drop(g);
        drop(r);

        std::thread::scope(|s| {
            let h1 = s.spawn(|| {
                buf.init_thread();
                let frame = buf.get_page_existing(42).expect("t1: page 42");
                frame.read_lock().page_id
            });
            let h2 = s.spawn(|| {
                buf.init_thread();
                let frame = buf.get_page_existing(42).expect("t2: page 42");
                frame.read_lock().page_id
            });

            assert_eq!(h1.join().expect("thread 1 panicked"), 42);
            assert_eq!(h2.join().expect("thread 2 panicked"), 42);
        });
    }

    /// Many threads race to load the same uncached page simultaneously.
    /// Every thread must get back the correct page_id and the directory must
    /// not be left in an inconsistent state.
    #[test]
    fn concurrent_load_of_uncached_page_all_threads_see_correct_page_id() {
        // Large buffer: enough frames so no eviction pressure during the race,
        // but page 99 starts uncached so all threads hit the slow path.
        let buf = PageBuffer::new(Arc::new(MemIO::new()), 64);
        buf.init_thread();

        // Seed page 99 in IO by allocating it dirty, then evicting it via fill.
        let (r, mut g) = buf.get_page_new(99).expect("seed page 99");
        g.dirty = true;
        drop(g);
        drop(r);
        {
            // 63 additional pages fill the remaining frames, forcing page 99 out.
            let mut refs = Vec::new();
            for id in 100..163u64 {
                refs.push(buf.get_page_new(id).expect("fill frame"));
            }
        } // all unpinned here; page 99 was evicted and flushed

        let results: std::sync::Mutex<Vec<u64>> = std::sync::Mutex::new(Vec::new());
        std::thread::scope(|s| {
            for _ in 0..8 {
                s.spawn(|| {
                    buf.init_thread();
                    let frame = buf.get_page_existing(99).expect("should load page 99");
                    results.lock().unwrap().push(frame.read_lock().page_id);
                });
            }
        });

        let ids = results.into_inner().unwrap();
        assert_eq!(ids.len(), 8, "all threads must complete");
        assert!(ids.iter().all(|&id| id == 99), "every thread must see page_id 99, got: {ids:?}");
    }
}
