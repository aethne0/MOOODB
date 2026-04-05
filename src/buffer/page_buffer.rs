use std::sync::atomic::{AtomicUsize, Ordering};

use parking_lot::RwLock;
use rustc_hash::FxHashMap;

use crate::{
    buffer::frame::{self, Frame, FrameRef},
    io,
    system::MmapBox,
};

type PageId = u64;

pub(crate) struct PageBuffer {
    pub(crate) io: Box<dyn crate::io::IODoer>,
    frames: MmapBox<[Frame]>,
    /// directory: page_id -> frame_index map, inflight map
    shard_dirs: Box<[RwLock<PageBufferShard>]>,
    eviction_hand: AtomicUsize,
}

pub(crate) struct PageBufferShard {
    page_frame_map: FxHashMap<PageId, usize>,
    inflight: FxHashMap<PageId, ()>,
}

// ● Public:
//   1. fetch_page(page_id) -> FrameRef — load from disk if not cached
//   2. new_page(page_id) -> FrameRef — allocate clean frame for a CoW-created page, mark dirty, no IO read
//   3. flush_page(page_id) -> Result<()> — write one dirty frame back
//   4. flush_all() -> Result<()> — checkpoint, flush every dirty frame

impl PageBuffer {
    pub(crate) fn new(io: Box<dyn io::IODoer>, frame_count: usize) -> Self {
        assert_ne!(frame_count, 0);

        let mut i = 0;
        let frames = MmapBox::<[Frame]>::new_slice_with(frame_count, || {
            let frame = Frame::new(i);
            i += 1;
            frame
        });

        let shard_dirs = Vec::from_iter((0..SHARD_CNT).into_iter().map(|_| {
            let mut map = FxHashMap::default();
            let mut inflight = FxHashMap::default();

            map.reserve(frame_count / SHARD_CNT);
            inflight.reserve(frame_count / SHARD_CNT);
            RwLock::new(PageBufferShard { page_frame_map: map, inflight })
        }))
        .into_boxed_slice();

        Self { io, frames, shard_dirs, eviction_hand: AtomicUsize::new(0) }
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    fn pin_frame(&self, frame_index: usize) -> FrameRef<'_> {
        self.frames[frame_index].pin(&self)
    }

    // ▄▄▄ . ▌ ▐·▪   ▄▄· ▄▄▄▄▄▪         ▐ ▄
    // ▀▄.▀·▪█·█▌██ ▐█ ▌▪•██  ██ ▪     •█▌▐█
    // ▐▀▀▪▄▐█▐█•▐█·██ ▄▄ ▐█.▪▐█· ▄█▀▄ ▐█▐▐▌
    // ▐█▄▄▌ ███ ▐█▌▐███▌ ▐█▌·▐█▌▐█▌.▐▌██▐█▌
    //  ▀▀▀ . ▀  ▀▀▀·▀▀▀  ▀▀▀ ▀▀▀ ▀█▄▀▪▀▀ █▪
    // Second-chance clock eviction

    /// Will get a free frame, evicting if neccessary
    /// This function handles all eviction logic (outside the initial scan)
    fn get_free_frame(&self, new_page_id: u64) -> FrameRef<'_> {
        loop {
            let frame_index = self.scan_for_eviction_candidate();
            let frame_ref = self.pin_frame(frame_index);

            // we'll optimistically try to get a lock on this frame - if we dont, then someone else
            // evicted this frame before we got a chance, so well try again and find another one
            if let Some(mut frame_guard) = frame_ref.try_write_lock() {
                if frame_guard.never_used() {
                    // if this is a unused frame (like on db startup) we can just take it
                    frame_guard.reinit(new_page_id);
                    let mut dir_guard = self.shard_dirs[hash(new_page_id)].write();
                    dir_guard.page_frame_map.insert(new_page_id, frame_index);
                    return frame_ref;
                } else {
                    // otherwise we need to do cleanup

                    if frame_guard.dirty {
                        todo!()
                    }

                    // get old and new shard locks - or just old if theyre the same
                    let (mut dir_guard_old, dir_guard_new_opt) = {
                        // we need to do this funny thing to ensure we take the locks in ascending
                        // order, because otherwise we could DEADLOCK in a scenario like:
                        // thread-A evicts frame from shard-3 to put in shard-1
                        // thread-B evicts frame from shard-1 to put in shard-3
                        // thread-A has lock on shard-3, thread-B has lock on shard-1
                        let old_shard = hash(frame_guard.page_id);
                        let new_shard = hash(new_page_id);

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
                        dir_guard_new.page_frame_map.insert(new_page_id, frame_index);
                        drop(dir_guard_new);
                    } else {
                        // remove old, insert new - but for same shard
                        dir_guard_old.page_frame_map.remove(&frame_guard.page_id);
                        dir_guard_old.page_frame_map.insert(new_page_id, frame_index);
                        drop(dir_guard_old);
                    }

                    frame_guard.reinit(new_page_id);
                    return frame_ref;
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

// magic shard hash thingy
const SHARD_CNT: usize = 64;

fn hash(mut page_id: u64) -> usize {
    page_id ^= page_id >> 33;
    page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
    page_id ^= page_id >> 33;
    (page_id as usize) & (SHARD_CNT - 1)
}

