use std::{
    ops::Deref,
    sync::atomic::{AtomicIsize, Ordering},
};

use crate::page::PAGE_SIZE;

#[repr(align(64))]
pub(crate) struct Frame<IOError> {
    pub(crate) pins: AtomicIsize,
    inner: tokio::sync::RwLock<FrameInner<IOError>>,
}

impl<IOError> Frame<IOError> {
    /// Increment the pin count and return a RAII [`FrameRef`] that decrements pin count on drop.
    #[must_use = "dropping this immediately unpins the frame"]
    pub(crate) fn pin(&self) -> FrameRef<'_, IOError> {
        FrameRef::new(self)
    }
}

impl<IOError> Default for Frame<IOError> {
    fn default() -> Self {
        Self {
            pins: AtomicIsize::new(0),
            inner: tokio::sync::RwLock::new(FrameInner {
                header: FrameHeader { page_id: 0, dirty: false },
                buffer: [0; PAGE_SIZE],
                ioerr: None,
            }),
        }
    }
}

pub(crate) struct FrameHeader {
    pub(crate) page_id: u64,
    pub(crate) dirty: bool,
}

pub(crate) struct FrameInner<IOError> {
    pub(crate) header: FrameHeader,
    pub(crate) buffer: [u8; PAGE_SIZE],
    /// This is for the loading-in task to flag waiting tasks that there was an
    /// IO error - abandon ship!
    pub(crate) ioerr: Option<IOError>,
}

pub(crate) struct FrameRef<'a, IOError> {
    frame: &'a Frame<IOError>,
}

impl<'a, IOError> FrameRef<'a, IOError> {
    fn new(frame: &'a Frame<IOError>) -> Self {
        frame.pins.fetch_add(1, Ordering::Relaxed);
        Self { frame }
    }

    /// Acquire the inner write lock unconditionally, bypassing the load-error check.
    /// Only for use by the task responsible for initially populating the frame.
    /// This initializes the frame as well (page_id, reset dirty flag, etc)
    pub(crate) async fn write_raw(&self, page_id: u64) -> tokio::sync::RwLockWriteGuard<'_, FrameInner<IOError>> {
        let mut guard = self.inner.write().await;
        guard.header.page_id = page_id;
        guard.header.dirty = false;
        guard.ioerr = None;
        guard
    }

    /// Acquire the inner read lock. Returns `None` if the frame had a load error.
    pub(crate) async fn read(&self) -> Option<tokio::sync::RwLockReadGuard<'_, FrameInner<IOError>>> {
        let guard = self.inner.read().await;
        if guard.ioerr.is_some() { None } else { Some(guard) }
    }

    /// Acquire the inner write lock. Returns `None` if the frame had a load error.
    pub(crate) async fn write(&self) -> Option<tokio::sync::RwLockWriteGuard<'_, FrameInner<IOError>>> {
        let guard = self.inner.write().await;
        if guard.ioerr.is_some() { None } else { Some(guard) }
    }
}

impl<IOError> Deref for FrameRef<'_, IOError> {
    type Target = Frame<IOError>;
    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl<IOError> Drop for FrameRef<'_, IOError> {
    fn drop(&mut self) {
        self.frame.pins.fetch_sub(1, Ordering::Relaxed);
    }
}
