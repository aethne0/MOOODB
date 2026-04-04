use std::sync::atomic::{AtomicUsize, Ordering};

use parking_lot::{Mutex, RwLock};
use rustc_hash::FxHashMap;

use crate::{
    buffer::{
        frame::{Frame, FrameRef},
        queue::Queue,
    },
    io,
    system::MmapBox,
};

type PageId = u64;

pub(crate) struct PageBuffer {
    pub(crate) io: Box<dyn crate::io::IODoer>,
    frames: MmapBox<[Frame]>,

    free_frames: Mutex<Queue<usize>>,
    eviction_hand: AtomicUsize,

    /// directory: page_id -> frame_index map, inflight map
    shard_dirs: FxHashMap<usize, RwLock<PageBufferShard>>,
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

        let mut free = Queue::new(frame_count);
        for i in 0..frame_count {
            free.push_back(i);
        }

        let mut i = 0;
        let frames = MmapBox::<[Frame]>::new_slice_with(frame_count, || {
            let frame = Frame::new(i);
            i += 1;
            frame
        });

        let shard_dirs = FxHashMap::from_iter((0..SHARD_CNT).into_iter().map(|shard_index| {
            let mut map = FxHashMap::default();
            let mut inflight = FxHashMap::default();
            map.reserve(frame_count / SHARD_CNT);
            inflight.reserve(frame_count / SHARD_CNT);
            (shard_index, RwLock::new(PageBufferShard { page_frame_map: map, inflight }))
        }));

        Self { io, frames, free_frames: Mutex::new(free), shard_dirs, eviction_hand: AtomicUsize::new(0) }
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    fn pin_frame(&self, frame_index: usize) -> FrameRef<'_> {
        self.frames[frame_index].pin(&self)
    }

    fn get_free_frame(&self) -> Option<FrameRef<'_>> {
        let frame_index_opt = self.free_frames.lock().pop_front();
        match frame_index_opt {
            None => {
                todo!()
            }
            Some(index) => Some(self.pin_frame(index)),
        }
    }

    // ▄▄▄ . ▌ ▐·▪   ▄▄· ▄▄▄▄▄▪         ▐ ▄
    // ▀▄.▀·▪█·█▌██ ▐█ ▌▪•██  ██ ▪     •█▌▐█
    // ▐▀▀▪▄▐█▐█•▐█·██ ▄▄ ▐█.▪▐█· ▄█▀▄ ▐█▐▐▌
    // ▐█▄▄▌ ███ ▐█▌▐███▌ ▐█▌·▐█▌▐█▌.▐▌██▐█▌
    //  ▀▀▀ . ▀  ▀▀▀·▀▀▀  ▀▀▀ ▀▀▀ ▀█▄▀▪▀▀ █▪
    // Second-chance clock eviction

    fn evict_frame(&self, frame_index: usize) -> Result<(), io::IOError> {
        todo!()
    }

    fn clock_evict(&self) {
        let to_evict = self.scan_for_eviction_candidate();
        todo!()
    }

    /// Scans for an eviction candidate (frame with 0 pins and 0 usage). This will spin until
    /// one is found. It is imperative that the caller re-check these conditions once a lock on the
    /// shard directory has been acquired, so we dont TOCTOU.
    fn scan_for_eviction_candidate(&self) -> usize {

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

            std::hint::spin_loop();
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
