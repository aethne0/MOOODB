use parking_lot::{Mutex, RwLock, RwLockReadGuard};
use rustc_hash::FxHashMap;

use crate::{
    buffer::{frame::Frame, queue::Queue},
    io,
    system::MmapBox,
};

type PageId = u64;

/// Rudimentary concurrent buffer manager
pub(crate) struct PageBuffer {
    io: Box<dyn crate::io::IODoer>,
    frames: MmapBox<[Frame]>,
    free: Mutex<Queue<usize>>,
    /// directory: page_id -> frame_index map, inflight map
    shard_dirs: FxHashMap<usize, RwLock<PagerShard>>,
}

pub(crate) struct PagerShard {
    page_frame_map: FxHashMap<PageId, usize>,
    inflight: FxHashMap<PageId, ()>,
}

impl PageBuffer {
    // magic shard hash thingy
    const SHARD_CNT: usize = 64;

    fn hash(mut page_id: u64) -> usize {
        page_id ^= page_id >> 33;
        page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
        page_id ^= page_id >> 33;
        (page_id as usize) & (Self::SHARD_CNT - 1)
    }

    pub(crate) fn new(io: Box<dyn io::IODoer>, frame_count: usize) -> Self {
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

        let shard_dirs = FxHashMap::from_iter((0..Self::SHARD_CNT).into_iter().map(|shard_index| {
            let mut map = FxHashMap::default();
            let mut inflight = FxHashMap::default();
            map.reserve(frame_count / Self::SHARD_CNT);
            inflight.reserve(frame_count / Self::SHARD_CNT);
            (shard_index, RwLock::new(PagerShard { page_frame_map: map, inflight }))
        }));

        Self { io, frames, free: Mutex::new(free), shard_dirs }
    }

    pub(crate) fn get_frame_by_page_id(&self, page_id: u64) -> Option<&'_ Frame> {
        let dir_guard = self.shard_dirs.get(&Self::hash(page_id)).unwrap().read();
        match dir_guard.page_frame_map.get(&page_id) {
            Some(&index) => Some(&self.frames[index]),
            None => None, // TODO evict
        }
    }
}

struct FrameRef<'a> {
    frame: &'a RwLockReadGuard<'a, Frame>,
    pager: &'a PageBuffer,
}

impl<'a> std::ops::Deref for FrameRef<'a> {
    type Target = RwLockReadGuard<'a, Frame>;

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl<'a> FrameRef<'a> {

}
