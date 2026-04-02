use std::{collections::HashMap, ops::Deref, sync::atomic::Ordering};

use crate::{
    buffer::{
        frame::{Frame, FrameInner},
        queue::Queue,
    },
    io,
    system::MmapBox,
};

type PageId = u64;

/// Rudimentary concurrent buffer manager
pub(crate) struct Pager {
    io: Box<dyn crate::io::IODoer>,
    frames: MmapBox<[Frame]>,
    /// directory: page_id -> frame_index map, free-list, inflight map
    dir: tokio::sync::RwLock<PagerInner>,
}

pub(crate) struct PagerInner {
    map: HashMap<PageId, usize>, // page_id -> frame_idx
    free: Queue<usize>,
    inflight: HashMap<PageId, tokio::sync::watch::Receiver<()>>,
}

impl Pager {
    #[must_use]
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

        Self {
            io,
            frames,
            dir: tokio::sync::RwLock::new(PagerInner {
                map: HashMap::with_capacity(frame_count),
                free,
                inflight: HashMap::with_capacity(256),
            }),
        }
    }

    pub(crate) fn get_free_frame<'a>(
        &'a self, guard: &mut tokio::sync::RwLockWriteGuard<'_, PagerInner>,
    ) -> Option<FrameRef<'a>> {
        // Look through (up to) entire free-list to find one that isnt currently pinned
        // (Some may still be pinned if there was an IO error and there are stragglers)
        for _ in 0..guard.free.len() {
            let index = guard.free.pop_front().unwrap(); // pop the next free frame_idx, if any

            let pin_count = self.frames[index].pins.load(Ordering::Acquire);

            if pin_count == 0 {
                return Some(self.pin_frame(index));
            } else {
                guard.free.push_back(index);
            }
        }

        // yikes we dont have any, better see if we can evict one
        let mut page_id_to_evict = None;
        for (&page_id, &frame_index) in guard.map.iter() {
            if self.frames[frame_index].pins.load(Ordering::Acquire) == 0 {
                page_id_to_evict = Some(page_id);
                break;
            }
        }

        match page_id_to_evict {
            Some(page_id) => {
                let frame_index = guard.map.remove(&page_id).unwrap();
                Some(self.pin_frame(frame_index))
            }
            None => None,
        }
    }

    pub(crate) async fn get_page_id<'a>(&'a self, page_id: u64) -> Option<FrameRef<'a>> {
        // 1. if the page already exists, or is already being fetched
        // in either of these cases the page WILL be in the `dir.map`
        let guard = self.dir.read().await;

        if let Some(&index) = guard.map.get(&page_id) {
            let frame_ref = self.pin_frame(index);

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
            let frameref = self.pin_frame(index);
            let rx_opt = guard.inflight.get(&page_id).cloned();
            drop(guard);

            if let Some(mut rx) = rx_opt {
                let _ = rx.changed().await;
            }

            return Some(frameref);
        }

        // at this point we have an exclusive lock and know that nobody else is fetching the page,
        // so well fetch it

        let Some(frame_ref) = self.get_free_frame(&mut guard) else {
            return None;
        };

        let (tx, rx) = tokio::sync::watch::channel(());
        guard.map.insert(page_id, frame_ref.frame_id());
        guard.inflight.insert(page_id, rx);

        // now we drop the directory guard - any tasks that come looking will sleep on inflight
        drop(guard);

        // do the actual io read into the frame - were only holding a write-lock on the frame
        let mut frame_guard = frame_ref.write_lock_raw(page_id).await;

        let io_err_res = self.io.read(page_id, &mut frame_guard.buffer).await;
        let was_error = io_err_res.is_err();
        frame_guard.io_err = io_err_res.err();

        drop(frame_guard); // no locks held.

        // take guard on directory, because if we dont then someone could see the
        // inflight entry after we tx.send
        let mut guard = self.dir.write().await;
        tx.send(()).expect("cant error, inflight has rx til we remove");
        guard.inflight.remove(&page_id);

        if was_error {
            guard.map.remove(&page_id);
            // we put this frame back in the free-list, even though some may still be pinning it
            // The pager will check that its unpinned before giving it out again
            guard.free.push_back(frame_ref.frame_id());
        }

        Some(frame_ref)
    }

    /// Increment the pin count and return a RAII [`FrameRef`] that decrements pin count on drop.
    fn pin_frame(&self, frame_index: usize) -> FrameRef<'_> {
        FrameRef::new(&self.frames[frame_index], &self)
    }
}

pub(crate) struct FrameRef<'a> {
    pager: &'a Pager,
    frame: &'a Frame,
}

impl<'a> FrameRef<'a> {
    fn new(frame: &'a Frame, pager: &'a Pager) -> Self {
        frame.pins.fetch_add(1, Ordering::Release);
        Self { frame, pager }
    }

    pub(crate) fn leak(&self) {
        self.pins.fetch_add(1, Ordering::Release);
    }

    /// Acquire the inner write lock unconditionally, bypassing the load-error check.
    /// Only for use by the task responsible for initially populating the frame.
    /// This initializes the frame as well (page_id, reset dirty flag, etc)
    pub(crate) async fn write_lock_raw(&self, page_id: u64) -> tokio::sync::RwLockWriteGuard<'_, FrameInner> {
        let mut guard = self.inner.write().await;
        guard.header.page_id = page_id;
        guard.header.dirty = false;
        guard.io_err = None;
        guard
    }

    /// Acquire the inner read lock. Returns `None` if the frame had a load error.
    pub(crate) async fn read_lock(&self) -> Option<tokio::sync::RwLockReadGuard<'_, FrameInner>> {
        let guard = self.inner.read().await;
        if guard.io_err.is_some() { None } else { Some(guard) }
    }

    /// Acquire the inner write lock. Returns `None` if the frame had a load error.
    pub(crate) async fn write_lock(&self) -> Option<tokio::sync::RwLockWriteGuard<'_, FrameInner>> {
        let guard = self.inner.write().await;
        if guard.io_err.is_some() { None } else { Some(guard) }
    }

    pub(crate) async fn io_write(&self, guard: tokio::sync::RwLockWriteGuard<'_, FrameInner>) {
        // TODO error etc
        self.pager.io.write(guard.header.page_id, &guard.buffer).await.unwrap();
    }
}

// TODO make guard wrapper type blah blah blah

impl Deref for FrameRef<'_> {
    type Target = Frame;
    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl Drop for FrameRef<'_> {
    fn drop(&mut self) {
        self.frame.pins.fetch_sub(1, Ordering::Release);
    }
}
