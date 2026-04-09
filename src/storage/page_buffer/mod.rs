pub(super) mod frame;
pub(super) mod io;
mod memory_alloc;

use std::cell::Cell;
use std::cell::RefCell;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use parking_lot::RwLock;
use rustc_hash::FxHashMap;
use zerocopy::FromZeros;

use super::pages::checksum;
use crate::storage::pages::PAGE_ID_NULL;
use frame::FrameReadGuard;
use frame::FrameSlab;
use frame::FrameWriteGuard;
use io::IODoer;
use io::IOFactory;

thread_local! {
    static THREAD_IO: RefCell<Option<Box<dyn IODoer>>> = RefCell::new(None);
}

static THREAD_TOKEN_PREFIX_NEXT: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static THREAD_TOKEN_PREFIX: u64
        = THREAD_TOKEN_PREFIX_NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    static THREAD_TOKEN_NEXT: Cell<u64> = const { Cell::new(0) };
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
const fn hash(mut page_id: u64) -> usize {
    page_id ^= page_id >> 33;
    page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
    page_id ^= page_id >> 33;
    (page_id as usize) & (SHARD_CNT - 1)
}

pub(super) struct PageBuffer {
    pub(super) io: Arc<dyn IOFactory>,
    framer: FrameSlab,
    /// All shards' maps of `page_id` -> `frame_index`
    shard_dirs: Box<[RwLock<PageBufferShard>]>,
    eviction_hand: AtomicUsize,

    /// we are not using this yet, just aborting when its set - eventually well use it
    poisoned: AtomicBool,
}

pub(super) struct PageBufferShard {
    // making this a struct incase we add more later - might flatten
    /// Shard's map of `page_id` -> `frame_index`
    dir: FxHashMap<u64, usize>,
}

impl PageBuffer {
    pub(super) fn new(io: Arc<dyn IOFactory>, frame_count: usize) -> Self {
        assert_ne!(frame_count, 0);

        let framer = FrameSlab::new(frame_count);

        let shard_dirs = (0..SHARD_CNT)
            .map(|_| {
                let mut map = FxHashMap::default();
                map.reserve(frame_count / SHARD_CNT);
                RwLock::new(PageBufferShard { dir: map })
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();

        Self { io, framer, shard_dirs, eviction_hand: AtomicUsize::new(0), poisoned: false.into() }
    }

    //  ▄▄▄· ▄▄▄·  ▄▄ • ▪   ▐ ▄  ▄▄ •
    // ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪██ •█▌▐█▐█ ▀ ▪
    //  ██▀·▄█▀▀█ ▄█ ▀█▄▐█·▐█▐▐▌▄█ ▀█▄
    // ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▌██▐█▌▐█▄▪▐█
    // .▀    ▀  ▀ ·▀▀▀▀ ▀▀▀▀▀ █▪·▀▀▀▀
    //  Paging & Eviction

    /// Fetches existing page
    pub(super) fn get_page_existing(&self, page_id: u64) -> Result<FrameReadGuard<'_>, std::io::ErrorKind> {
        let shard = hash(page_id);

        // if its already paged in
        let shard_guard = self.shard_dirs[shard].read();
        if let Some(&frame_index) = shard_guard.dir.get(&page_id) {
            return Ok(self.framer.pin_read(frame_index));
        }
        drop(shard_guard);

        // we need to page it in and load it

        // this puts it in the dir right away, which is useful because other threads can see we
        // already have inflight io
        let mut frame_guard = self.get_free_frame();

        // we now need to make entry for this page in directory
        let mut dir_guard = self.shard_dirs[shard].write();

        // check if another thread beat us to populating this page_id in the dir
        // well abandon our frame and use theres instead
        if let Some(&found_frame_index) = dir_guard.dir.get(&page_id) {
            // we need to set our frame to uninit, to make sure another frame doesnt later choose
            // it for eviction, see its page_id, then remove that page_id from the dir
            // (the page_id is the same as the actual frame that were going to take!)
            frame_guard.cancel();

            let frame_guard = self.framer.pin_read(found_frame_index);
            // if the frame we adopt has an error we just return that error - no retry
            if let Some(err) = frame_guard.get_read_error() {
                return Err(err);
            }

            return Ok(frame_guard);
        }

        dir_guard.dir.insert(page_id, frame_guard.index());
        self.framer[frame_guard.index()]
            .page_id_hint
            .store(page_id, Ordering::Release);
        drop(dir_guard);

        // fetch data
        let res = Self::io_read_one(&mut frame_guard, page_id);
        match res {
            Ok(()) => Ok(self.framer.downgrade_write_guard(frame_guard)),
            Err(err) => {
                let frame_index = frame_guard.index();
                // Remove from dir and clear hint before releasing the frame
                let mut shard_guard = self.shard_dirs[shard].write();
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
    pub(super) fn get_page_new(&self, new_page_id: u64) -> FrameWriteGuard<'_> {
        let mut frame_guard = self.get_free_frame();

        frame_guard.buffer.zero();
        frame_guard.state_uninit_to_writeable(new_page_id);

        let mut dir_guard = self.shard_dirs[hash(new_page_id)].write();
        debug_assert!(!dir_guard.dir.contains_key(&new_page_id), "page was already in directory");
        dir_guard.dir.insert(new_page_id, frame_guard.index());
        self.framer[frame_guard.index()]
            .page_id_hint
            .store(new_page_id, Ordering::Release);

        frame_guard
    }

    /// Gets, pins, and writelocks and unused frame
    /// Maybe evicts a frame
    /// **NOTE**: it may contain dirty data, and its fields will not be initialized correctly
    /// (page_id, dirty, is_err)**
    // **NOTE**: this will always give a frame in the Uninitialized state
    fn get_free_frame(&self) -> FrameWriteGuard<'_> {
        loop {
            let frame_index = self.scan_for_eviction_candidate();

            // Read the hint to find which shard to lock. We must lock the shard BEFORE the frame
            // to match the ordering in get_page_existing (shard → frame), avoiding deadlock.
            let hint = self.framer[frame_index].page_id_hint.load(Ordering::Acquire);
            let mut opt_dir_guard = match hint {
                PAGE_ID_NULL => None,
                _ => Some(self.shard_dirs[hash(hint)].write()),
            };

            let mut frame_guard = self.framer.pin_write(frame_index);

            if self.framer.pin_count(frame_index, Ordering::Acquire) != 1 {
                // Someone else pinned this frame between our scan and now; try again.
                frame_guard.release();
                continue;
            }

            if let Some(actual_page_id) = frame_guard.has_valid_page() {
                // If the hint was stale and pointed to the wrong shard, we can't safely remove
                // the directory entry — we'd be holding the wrong shard lock. Retry.
                if opt_dir_guard.is_none() || hash(hint) != hash(actual_page_id) {
                    frame_guard.release();
                    continue;
                }

                opt_dir_guard.as_mut().unwrap().dir.remove(&actual_page_id);
                self.framer[frame_index]
                    .page_id_hint
                    .store(PAGE_ID_NULL, Ordering::Release);
                drop(opt_dir_guard);

                if frame_guard.is_dirty() {
                    self.io_write_one(&mut frame_guard);
                }
            }
            // If has_valid_page() is None the frame is already Uninitialized/ReadErrored with no
            // directory entry. opt_dir_guard (if any from a stale hint) just drops here.

            frame_guard.state_to_uninit();
            return frame_guard;
        }
    }

    /// Scans for an eviction candidate (frame with 0 pins and 0 usage). This will spin until
    /// one is found. It is imperative that the caller re-check these conditions once a lock on the
    /// shard directory has been acquired, so we dont TOCTOU.
    fn scan_for_eviction_candidate(&self) -> usize {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            let frame_index = self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.framer.len();
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
            if checked_count == self.framer.len() {
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
            *cell.borrow_mut() = Some(self.io.make_io_doer());
        });
    }

    pub(super) fn thread_io<F, R>(f: F) -> R
    where
        F: FnOnce(&dyn IODoer) -> R,
    {
        THREAD_IO.with(|cell| f(cell.borrow().as_deref().expect("init_thread not called")))
    }

    fn io_read_one(frame_guard: &mut FrameWriteGuard<'_>, page_id: u64) -> Result<(), std::io::ErrorKind> {
        let res = Self::thread_io(|io| {
            debug_assert_eq!(io.peek(), 0, "queue was dirty before we submitted anything?");
            let token = next_thread_token();
            unsafe { io.submit_read(token, page_id, frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token, "received a token other than the one we submitted - queue was dirty?");
            if let Err(err) = res {
                tracing::error!("Read-in Error! Error: {}", err);
            }
            res
        });

        // check checksum
        if !checksum::check(frame_guard.buffer) {
            return Err(std::io::ErrorKind::UnexpectedEof); // TODO error type
        }

        frame_guard.state_uninit_to_read(page_id, res);
        res
    }

    fn io_write_one(&self, frame_guard: &mut FrameWriteGuard<'_>) {
        checksum::set(frame_guard.buffer);

        Self::thread_io(|io| {
            debug_assert_eq!(io.peek(), 0, "queue was dirty before we submitted anything?");
            let token = next_thread_token();
            unsafe { io.submit_write(token, frame_guard.get_page_id(), frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token, "received a token other than the one we submitted - queue was dirty?");

            if let Err(err) = res {
                tracing::error!("Write-out Error! Database will be poisoned. Error: {}", err);
                self.poisoned.store(true, Ordering::Relaxed);
                std::process::abort(); // TODO eventually this will be handled by `poisoned` instead
            }
        });

        // we are setting this even if we get an err, because if we had an err we are going to
        // poison the whole page-buffer anyway
        frame_guard.state_dirty_to_written();
    }
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
    use io::mem_io::MemIO;

    fn make_buffer(frame_count: usize) -> PageBuffer {
        let io = Arc::new(MemIO::new());
        let buf = PageBuffer::new(io, frame_count);
        buf.init_thread();
        buf
    }

    #[test]
    fn new_page_is_zeroed() {
        let buf = make_buffer(4);

        let guard = buf.get_page_new(1);

        assert!(guard.buffer.iter().all(|&b| b == 0));
        guard.commit();
    }

    #[test]
    fn committed_write_readable_from_buffer() {
        let buf = make_buffer(4);

        let guard = buf.get_page_new(1);
        guard.buffer[0] = 0xAB;
        guard.buffer[100] = 0xCD;
        guard.commit();

        let read = buf.get_page_existing(1).expect("page should be in buffer");
        assert_eq!(read.buffer[0], 0xAB);
        assert_eq!(read.buffer[100], 0xCD);
    }

    #[test]
    fn pages_have_isolated_data() {
        let buf = make_buffer(8);

        for page_id in 0..4u64 {
            let guard = buf.get_page_new(page_id);
            guard.buffer[0] = page_id as u8;
            guard.commit();
        }

        for page_id in 0..4u64 {
            let read = buf.get_page_existing(page_id).expect("page should be readable");
            assert_eq!(read.buffer[0], page_id as u8, "page {page_id} had wrong data");
            assert!(
                read.buffer[1..].iter().all(|&b| b == 0),
                "page {page_id} has unexpected non-zero bytes past index 0"
            );
        }
    }

    // Fills a 2-frame buffer, then forces eviction by allocating a third page.
    // The evicted frame must have been written to IO, so both original pages
    // remain readable (one from buffer, one reloaded from IO).
    #[test]
    fn evicted_dirty_page_is_flushed_and_readable() {
        let buf = make_buffer(2);

        let g0 = buf.get_page_new(0);
        g0.buffer[0] = 10;
        g0.commit();

        let g1 = buf.get_page_new(1);
        g1.buffer[0] = 20;
        g1.commit();

        // Third allocation: clock decrements both frames' usage to 0 then evicts one.
        let g2 = buf.get_page_new(2);
        g2.commit();

        let r0 = buf.get_page_existing(0).expect("page 0 should be readable");
        assert_eq!(r0.buffer[0], 10, "page 0 data wrong after eviction");
        drop(r0);

        let r1 = buf.get_page_existing(1).expect("page 1 should be readable");
        assert_eq!(r1.buffer[0], 20, "page 1 data wrong after eviction");
    }

    // Regression test for the shard→frame lock ordering deadlock.
    //
    // Before the fix, get_page_existing held a shard lock while acquiring a frame
    // lock (shard → frame), while get_free_frame held a frame lock while acquiring
    // the shard lock (frame → shard). Under concurrent access this could deadlock.
    //
    // With the fix, get_free_frame reads page_id_hint to determine which shard to
    // lock first, making the ordering consistently shard → frame everywhere.
    #[test]
    fn concurrent_reads_with_eviction_do_not_deadlock() {
        const FRAMES: usize = 4;
        const TOTAL_PAGES: u64 = 16;

        let buf = Arc::new(make_buffer(FRAMES));

        // Pre-populate more pages than fit in the buffer, triggering evictions.
        for page_id in 0..TOTAL_PAGES {
            let g = buf.get_page_new(page_id);
            g.commit();
        }

        // Spawn threads that concurrently read all pages. With TOTAL_PAGES > FRAMES,
        // reads will trigger evictions under contention — the scenario that used to deadlock.
        let threads: Vec<_> = (0..4)
            .map(|_| {
                let buf = Arc::clone(&buf);
                std::thread::spawn(move || {
                    buf.init_thread();
                    for page_id in 0..TOTAL_PAGES {
                        let _guard = buf.get_page_existing(page_id).expect("page should load");
                    }
                })
            })
            .collect();

        for t in threads {
            t.join().expect("thread panicked");
        }
    }

    #[test]
    fn concurrent_independent_writes_do_not_deadlock() {
        const FRAMES: usize = 8;
        const PAGES_PER_THREAD: u64 = 8;
        const THREAD_COUNT: u64 = 4;

        // Don't call init_thread on the main thread — the spawned threads own this buffer.
        let buf = Arc::new(PageBuffer::new(Arc::new(MemIO::new()), FRAMES));

        // Each thread writes a disjoint range of page IDs to avoid races on get_page_new.
        let threads: Vec<_> = (0..THREAD_COUNT)
            .map(|t| {
                let buf = Arc::clone(&buf);
                std::thread::spawn(move || {
                    buf.init_thread();
                    let base = t * PAGES_PER_THREAD;
                    for page_id in base..base + PAGES_PER_THREAD {
                        let g = buf.get_page_new(page_id);
                        g.buffer[0] = page_id as u8;
                        g.commit();
                    }
                })
            })
            .collect();

        for t in threads {
            t.join().expect("thread panicked");
        }
    }
}
