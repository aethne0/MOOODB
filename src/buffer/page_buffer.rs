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
    buffer::frame::{Frame, FrameReadGuard, FrameRef, FrameWriteGuard},
    io,
    system::MmapBox,
};

thread_local! {
    static THREAD_IO: RefCell<Option<Box<dyn io::IODoer>>> = RefCell::new(None);
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

type PageId = u64;

pub(crate) struct PageBuffer {
    pub(crate) io: Arc<dyn crate::io::IOFactory>,
    frames: MmapBox<[Frame]>,
    /// directory: page_id -> frame_index map, inflight map
    shard_dirs: Box<[RwLock<PageBufferShard>]>,
    eviction_hand: AtomicUsize,
}

pub(crate) struct PageBufferShard {
    // making this a struct incase we add more later - might flatten
    page_frame_map: FxHashMap<PageId, usize>,
}

const SHARD_CNT: usize = 64;
fn hash(mut page_id: u64) -> usize {
    page_id ^= page_id >> 33;
    page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
    page_id ^= page_id >> 33;
    (page_id as usize) & (SHARD_CNT - 1)
}

//   todo:
//   3. flush_page(page_id) -> Result<()> — write one dirty frame back
//   4. flush_all() -> Result<()> — checkpoint, flush every dirty frame

impl PageBuffer {
    pub(crate) fn new(io: Arc<dyn io::IOFactory>, frame_count: usize) -> Self {
        assert_ne!(frame_count, 0);

        let mut i = 0;
        let frames = MmapBox::<[Frame]>::new_slice_with(frame_count, || {
            let frame = Frame::new(i);
            i += 1;
            frame
        });

        let shard_dirs = Vec::from_iter((0..SHARD_CNT).into_iter().map(|_| {
            let mut map = FxHashMap::default();
            map.reserve(frame_count / SHARD_CNT);
            RwLock::new(PageBufferShard { page_frame_map: map })
        }))
        .into_boxed_slice();

        Self { io, frames, shard_dirs, eviction_hand: AtomicUsize::new(0) }
    }

    // ▪
    // ██ ▪
    // ▐█· ▄█▀▄
    // ▐█▌▐█▌.▐▌
    // ▀▀▀ ▀█▄▀▪

    /// Must be called once by each worker thread before using the buffer.
    pub(crate) fn init_thread(&self) {
        THREAD_IO.with(|cell| {
            assert!(cell.borrow().is_none(), "Tried to init thread-io twice!");
            *cell.borrow_mut() = Some(self.io.make_io_doer())
        });
    }

    pub(crate) fn thread_io<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&dyn io::IODoer) -> R,
    {
        THREAD_IO.with(|cell| f(cell.borrow().as_deref().expect("init_thread not called")))
    }

    fn io_read_one(&self, frame_guard: &mut FrameWriteGuard<'_>) -> Result<(), std::io::ErrorKind> {
        self.thread_io(|io| {
            debug_assert_eq!(io.peek(), 0);
            let token = next_thread_token();
            unsafe { io.submit_read(token, frame_guard.page_id, &mut frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token);
            res
        })
    }

    // todo merge these
    fn io_write_one(&self, frame_guard: &FrameReadGuard<'_>) -> Result<(), std::io::ErrorKind> {
        self.thread_io(|io| {
            debug_assert_eq!(io.peek(), 0);
            let token = next_thread_token();
            unsafe { io.submit_write(token, frame_guard.page_id, &frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token);
            res
        })
    }

    // todo merge these
    fn io_write_one_w(&self, frame_guard: &FrameWriteGuard<'_>) -> Result<(), std::io::ErrorKind> {
        self.thread_io(|io| {
            debug_assert_eq!(io.peek(), 0);
            let token = next_thread_token();
            unsafe { io.submit_write(token, frame_guard.page_id, &frame_guard.buffer) };
            io.flush();
            let (recv_token, res) = io.reap_one();
            debug_assert_eq!(recv_token, token);
            res
        })
    }

    //  ▄▄▄· ▄▄▄·  ▄▄ • ▪   ▐ ▄  ▄▄ •
    // ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪██ •█▌▐█▐█ ▀ ▪
    //  ██▀·▄█▀▀█ ▄█ ▀█▄▐█·▐█▐▐▌▄█ ▀█▄
    // ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▌██▐█▌▐█▄▪▐█
    // .▀    ▀  ▀ ·▀▀▀▀ ▀▀▀▀▀ █▪·▀▀▀▀

    /// Gives an empty frame with a new page
    /// Does not mark the frame as dirty!
    /// Frames should only be marked dirty once you actually want them to be written out.
    ///
    /// **Note**: The writeguard that this returns will have been held since BEFORE the frame was
    /// inserted into the page directory
    pub(crate) fn get_page_new(&self, new_page_id: u64) -> (FrameRef<'_>, FrameWriteGuard<'_>) {
        let (a, b) = self.get_free_frame().unwrap();
        todo!()
    }

    /// Fetches existing page
    pub(crate) fn get_page_existing(&self, page_id: u64) -> Result<FrameRef<'_>, std::io::ErrorKind> {
        let shard = hash(page_id);

        // if its already paged in
        let shard_guard = self.shard_dirs[shard].read();
        if let Some(&frame_index) = shard_guard.page_frame_map.get(&page_id) {
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

        let res = self.io_read_one(&mut frame_guard);
        match res {
            Ok(()) => Ok(frame_ref),
            Err(err) => {
                self.shard_dirs[shard].write().page_frame_map.remove(&page_id);
                frame_guard.io_err = Some(err.clone());
                Err(err)
            }
        }
    }

    /// Gets, pins, and writelocks and unused frame
    /// **NOTE: it may contain dirty data, and its fields will not be initialized correctly
    /// (page_id, dirty, is_err)**
    fn get_free_frame(&self) -> Result<(FrameRef<'_>, FrameWriteGuard<'_>), std::io::ErrorKind> {
        loop {
            let frame_index = self.scan_for_eviction_candidate();
            let frame_ref = self.frames[frame_index].pin();

            // we'll optimistically try to get a lock on this frame - if we dont, then someone else
            // evicted this frame before we got a chance, so well try again and find another one
            if let Some(mut frame_guard) = frame_ref.try_write_lock() {
                if !frame_guard.never_used() {
                    let mut dir_guard = self.shard_dirs[hash(frame_guard.page_id)].write();

                    if frame_ref.pins.load(Ordering::Acquire) != 1 {
                        // we need to recheck pins again after we take the old directory lock, to make
                        // sure nobody found this and pinned it in the meantime
                        // If someone did we drop all our locks and start over
                        continue;
                    }

                    dir_guard.page_frame_map.remove(&frame_guard.page_id);
                    drop(dir_guard);

                    if frame_guard.dirty {
                        if let Err(err) = self.io_write_one_w(&frame_guard) {
                            return Err(err);
                        }
                        frame_guard.dirty = false;
                    }
                }

                return Ok((frame_ref, frame_guard));
            }
        }
    }

    /// Will get a free frame, evicting if neccessary
    /// This function handles all eviction logic (outside the initial scan)
    ///
    /// **Note**: The writeguard that this returns will have been held since BEFORE the frame was
    /// inserted into the page directory
    fn get_free_frame_2(&self, req_page_id: u64) -> (FrameRef<'_>, FrameWriteGuard<'_>) {
        loop {
            let frame_index = self.scan_for_eviction_candidate();
            let frame_ref = self.frames[frame_index].pin();

            // we'll optimistically try to get a lock on this frame - if we dont, then someone else
            // evicted this frame before we got a chance, so well try again and find another one
            if let Some(mut frame_guard) = frame_ref.try_write_lock() {
                if frame_guard.never_used() {
                    // if this is a unused frame (like on db startup) we can just take it
                    frame_guard.reinit(req_page_id);
                    let mut dir_guard = self.shard_dirs[hash(req_page_id)].write();
                    match dir_guard.page_frame_map.get(&req_page_id) {
                        Some(&frame_index) => {
                            drop(frame_guard);
                            let frame_ref = self.frames[frame_index].pin();
                            let frame_guard = frame_ref.write_lock();
                            return (frame_ref, frame_guard);
                        }
                        None => {
                            dir_guard.page_frame_map.insert(req_page_id, frame_index);
                            return (frame_ref, frame_guard);
                        }
                    }
                } else {
                    // otherwise we need to do cleanup

                    if frame_guard.dirty {
                        let res = self.io_write_one_w(&frame_guard); // TODO
                        frame_guard.dirty = false;
                    }

                    // get old and new shard locks - or just old if theyre the same
                    let (mut dir_guard_old, dir_guard_new_opt) = {
                        // we need to do this funny thing to ensure we take the locks in ascending
                        // order, because otherwise we could DEADLOCK in a scenario like:
                        // thread-A evicts frame from shard-3 to put in shard-1
                        // thread-B evicts frame from shard-1 to put in shard-3
                        // thread-A has lock on shard-3, thread-B has lock on shard-1
                        let old_shard = hash(frame_guard.page_id);
                        let new_shard = hash(req_page_id);

                        if old_shard < new_shard {
                            let old_guard = self.shard_dirs[old_shard].write();
                            let new_guard = self.shard_dirs[new_shard].write();
                            (old_guard, Some(new_guard))
                        } else if old_shard > new_shard {
                            // if theyre == this is fine too ofc
                            let new_guard = self.shard_dirs[new_shard].write();
                            let old_guard = self.shard_dirs[old_shard].write();
                            (old_guard, Some(new_guard))
                        } else {
                            let old_guard = self.shard_dirs[old_shard].write();
                            (old_guard, None)
                        }
                    };

                    if frame_ref.pins.load(Ordering::Acquire) != 1 {
                        // we need to recheck pins again after we take the old directory lock, to make
                        // sure nobody found this and pinned it in the meantime
                        // If someone did we drop all our locks and start over
                        continue;
                    }

                    if let Some(mut dir_guard_new) = dir_guard_new_opt {
                        // remove old, insert new
                        dir_guard_old.page_frame_map.remove(&frame_guard.page_id);
                        drop(dir_guard_old);
                        dir_guard_new.page_frame_map.insert(req_page_id, frame_index);
                        drop(dir_guard_new);
                    } else {
                        // remove old, insert new - but for same shard
                        dir_guard_old.page_frame_map.remove(&frame_guard.page_id);
                        dir_guard_old.page_frame_map.insert(req_page_id, frame_index);
                        drop(dir_guard_old);
                    }

                    frame_guard.reinit(req_page_id);
                    return (frame_ref, frame_guard);
                }
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
}
