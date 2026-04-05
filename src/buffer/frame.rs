use std::sync::atomic::{AtomicI16, AtomicU8, Ordering};

use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::page::PAGE_SIZE;

#[repr(align(64))]
pub(crate) struct Frame {
    frame_id: usize,
    pub(crate) usage: AtomicU8,
    pub(crate) pins: AtomicI16,
    pub(crate) inner: RwLock<FrameInner>,
}

const PAGE_ID_UNINIT: u64 = u64::MAX;

impl Frame {
    pub(crate) fn new(frame_id: usize) -> Self {
        Self {
            frame_id,
            usage: AtomicU8::new(0),
            pins: AtomicI16::new(0),
            inner: RwLock::new(FrameInner {
                buffer: [0; PAGE_SIZE],

                page_id: PAGE_ID_UNINIT,
                dirty: false,
                io_err: None,
            }),
        }
    }

    pub(crate) fn frame_id(&self) -> usize {
        self.frame_id
    }
}

impl<'a> Frame {
    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(crate) fn pin(&'a self) -> FrameRef<'a> {
        self.pins.fetch_add(1, Ordering::Release);
        self.usage.fetch_add(1, Ordering::Relaxed);
        FrameRef { frame: self }
    }
}

#[repr(align(64))]
pub(crate) struct FrameInner {
    pub(crate) buffer: [u8; PAGE_SIZE],

    pub(crate) page_id: u64,
    pub(crate) dirty: bool,
    /// This is for the loading-in task to flag waiting tasks that there was an
    /// IO error - abandon ship!
    pub(crate) io_err: Option<std::io::ErrorKind>,
}

impl FrameInner {
    pub(crate) fn never_used(&self) -> bool {
        self.page_id == PAGE_ID_UNINIT
    }

    /// sets new page_id and cleans up dirty and io_err (false, none)
    pub(crate) fn reinit(&mut self, page_id: u64) {
        self.page_id = page_id;
        self.dirty = false;
        self.io_err = None;
    }
}

/// RAII Ref to a frame - decrements frame pin counter on [`Drop`]
pub(crate) struct FrameRef<'a> {
    frame: &'a Frame,
}

impl<'a> FrameRef<'a> {
    #[must_use = "RAII FrameReadGuard unpins when dropped"]
    pub(crate) fn read_lock(&self) -> FrameReadGuard<'a> {
        FrameReadGuard { frame: self.frame.inner.read() }
    }

    #[must_use = "RAII FrameReadGuard unpins when dropped"]
    pub(crate) fn try_read_lock(&self) -> Option<FrameReadGuard<'a>> {
        let guard_opt = self.frame.inner.try_read();
        match guard_opt {
            Some(guard) => Some(FrameReadGuard { frame: guard }),
            None => None,
        }
    }

    #[must_use = "RAII FrameWriteGuard unpins when dropped"]
    pub(crate) fn write_lock(&self) -> FrameWriteGuard<'a> {
        FrameWriteGuard { frame: self.frame.inner.write() }
    }

    #[must_use = "RAII FrameReadGuard unpins when dropped"]
    pub(crate) fn try_write_lock(&self) -> Option<FrameWriteGuard<'a>> {
        let guard_opt = self.frame.inner.try_write();
        match guard_opt {
            Some(guard) => Some(FrameWriteGuard { frame: guard }),
            None => None,
        }
    }
}

impl<'a> std::ops::Deref for FrameRef<'a> {
    type Target = Frame;

    fn deref(&self) -> &Self::Target {
        &self.frame
    }
}

impl<'a> Drop for FrameRef<'a> {
    fn drop(&mut self) {
        self.frame.pins.fetch_sub(1, Ordering::Release);
    }
}

pub(crate) struct FrameReadGuard<'a> {
    frame: RwLockReadGuard<'a, FrameInner>,
}

impl<'a> std::ops::Deref for FrameReadGuard<'a> {
    type Target = RwLockReadGuard<'a, FrameInner>;

    fn deref(&self) -> &Self::Target {
        &self.frame
    }
}

pub(crate) struct FrameWriteGuard<'a> {
    frame: RwLockWriteGuard<'a, FrameInner>,
}

impl<'a> std::ops::Deref for FrameWriteGuard<'a> {
    type Target = RwLockWriteGuard<'a, FrameInner>;

    fn deref(&self) -> &Self::Target {
        &self.frame
    }
}

impl<'a> std::ops::DerefMut for FrameWriteGuard<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.frame
    }
}
