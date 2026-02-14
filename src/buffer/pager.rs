use std::collections::HashMap;

// TODO: shard

use crate::buffer::{
    fixed_queue::FixedQueue,
    frame::{Frame, FrameRef},
    io::IODoer,
};

type PageId = u64;
type FrameIndex = usize;

pub(crate) struct Pager<const FRAME_COUNT: usize, IO: IODoer> {
    io: IO,
    frames: crate::system::MmapBox<[Frame<IO::Error>; FRAME_COUNT]>,
    /// directory: page_id -> frame_index map, free-list, inflight map
    dir: tokio::sync::RwLock<PagerInner<FRAME_COUNT>>,
}

pub(crate) struct PagerInner<const FRAME_COUNT: usize> {
    map: HashMap<PageId, usize>, // page_id -> frame_idx
    free: FixedQueue<FrameIndex, FRAME_COUNT>,
    inflight: HashMap<PageId, tokio::sync::watch::Receiver<()>>,
}

impl<const FRAME_COUNT: usize> PagerInner<FRAME_COUNT> {
    fn next_free_frame(&mut self) -> Option<usize> {
        self.free.pop_front()
    }
}

impl<const FRAME_COUNT: usize, IO: IODoer> Pager<FRAME_COUNT, IO> {
    #[must_use]
    pub(crate) fn new(io: IO) -> Self {
        let mut free = FixedQueue::new();
        for i in 0..FRAME_COUNT {
            free.push_back(i);
        }

        Self {
            io,
            frames: crate::system::MmapBox::new_array_default(),
            dir: tokio::sync::RwLock::new(PagerInner {
                map: HashMap::with_capacity(FRAME_COUNT),
                free,
                inflight: HashMap::with_capacity(256),
            }),
        }
    }

    pub(crate) async fn get_free_frame<'a>(&'a self) -> Option<FrameRef<'a, IO::Error>> {
        let mut guard = self.dir.write().await; // take write guard
        let index_opt = guard.free.pop_front(); // pop the next free frame_idx, if any
        index_opt.map(|index| self.frames[index].pin()) // return Some(frameRef) or None
    }

    pub(crate) async fn get_page_id<'a>(&'a self, page_id: u64) -> Option<FrameRef<'a, IO::Error>> {
        // 1. if the page already exists, or is already being fetched
        // in either of these cases the page WILL be in the `dir.map`

        let guard = self.dir.read().await;

        if let Some(&index) = guard.map.get(&page_id) {
            let frame_ref = self.frames[index].pin();

            // see if theres an inflight struct
            let rx_opt = guard.inflight.get(&page_id).cloned();
            drop(guard);

            // if there was an inflight struct, sleep on it
            if let Some(mut rx) = rx_opt {
                // even if we get an error that just means the inflight struct was dropped - either way
                // we know that the fetch is "done"
                let _ = rx.changed().await;
            }

            // we now have the pinned page, and may or may not have slept while waiting for it to
            // be fetched
            // either way, well now just return the page.
            return Some(frame_ref);
        } else {
            drop(guard);
        }

        // 2. ok, so we didnt find the page, so well have to take a write-lock and fetch it ourselves

        let mut guard = self.dir.write().await;

        // unfortunately someone else may have inserted the page into the directory while we were
        // upgrading our lock, so we have to recheck

        if let Some(&index) = guard.map.get(&page_id) {
            let frameref = self.frames[index].pin();
            let rx_opt = guard.inflight.get(&page_id).cloned();
            drop(guard);

            if let Some(mut rx) = rx_opt {
                let _ = rx.changed().await;
            }

            return Some(frameref);
        }

        // at this point we have an exclusive lock and know that nobody else is fetching the page,
        // so well fetch it

        let Some(frame_index) = guard.next_free_frame() else {
            return None;
        };

        let frame_ref = self.frames[frame_index].pin();

        let (tx, rx) = tokio::sync::watch::channel(());
        guard.map.insert(page_id, frame_index);
        guard.inflight.insert(page_id, rx);

        // now we drop the directory guard - any tasks that come looking will sleep on inflight
        drop(guard);

        let mut frame_guard = frame_ref.write_raw(page_id).await;
        let mut errored = false;
        if let Err(ioerr) = self.io.read(page_id, &mut frame_guard.buffer).await {
            frame_guard.ioerr = Some(ioerr);
            errored = true;
        }

        drop(frame_guard);

        tx.send(()).expect("cant error, inflight has rx til we remove");

        let mut guard = self.dir.write().await;
        guard.inflight.remove(&page_id);
        if errored {
            guard.map.remove(&page_id); // TODO
        }

        Some(frame_ref)
    }
}
