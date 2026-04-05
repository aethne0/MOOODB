use std::sync::atomic::{AtomicI16, AtomicU8, Ordering};

use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::page::PAGE_SIZE;

#[repr(align(64))]
pub(crate) struct Frame {
    frame_id: usize,
    pub(super) usage: AtomicU8,
    pub(super) pins: AtomicI16,
    pub(super) inner: RwLock<FrameInner>,
}

const PAGE_ID_UNINIT: u64 = u64::MAX;

impl Frame {
    pub(super) fn new(frame_id: usize) -> Self {
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

    pub(super) fn index(&self) -> usize {
        self.frame_id
    }
}

impl<'a> Frame {
    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(super) fn pin(&'a self) -> FrameRef<'a> {
        self.pins.fetch_add(1, Ordering::Release);
        self.usage.fetch_add(1, Ordering::Relaxed);
        FrameRef { frame: self }
    }

    pub(super) fn leak(&'a self) {
        self.pins.fetch_add(1, Ordering::Release);
    }
}

#[repr(align(64))]
pub(crate) struct FrameInner {
    pub(super) buffer: [u8; PAGE_SIZE],

    pub(super) page_id: u64,
    pub(super) dirty: bool,
    /// This is for the loading-in task to flag waiting tasks that there was an
    /// IO error - abandon ship!
    pub(super) io_err: Option<std::io::ErrorKind>,
}

impl FrameInner {
    /// When frames are created at DB creation, page_ids are set to a sentinel "None" value
    /// ([`PAGE_ID_UNINIT`]), this checks if they are still that value. Pages can be reset back to this
    /// state as well if needed, using [`uninit`], namely during [`PageBuffer::get_new_frame`] if we
    /// have decide to abandon our frame - we need to clear its page_id so we don't erroneously see
    /// it later and remove its old `page_id` from the dir
    pub(super) fn has_non_init_page(&self) -> bool {
        self.page_id != PAGE_ID_UNINIT
    }

    /// sets new `page_id` and cleans up `dirty` and `io_err` (`false`, `none`)
    pub(super) fn reinit(&mut self, page_id: u64) {
        self.page_id = page_id;
        self.dirty = false;
        self.io_err = None;
    }

    /// Reinitializes the page using the "never initialized" sentinel `page_id` value
    /// ([`PAGE_ID_UNINIT`]). See [`FrameInner::has_non_init_page`] for more info.
    pub(super) fn uninit(&mut self) {
        self.reinit(PAGE_ID_UNINIT);
    }
}

/// RAII Ref to a frame - decrements frame pin counter on [`Drop`]
pub(crate) struct FrameRef<'a> {
    frame: &'a Frame,
}

impl<'a> FrameRef<'a> {
    #[must_use = "RAII FrameReadGuard unpins when dropped"]
    pub(super) fn read_lock(&self) -> FrameReadGuard<'a> {
        FrameReadGuard { frame: self.frame.inner.read() }
    }

    #[must_use = "RAII FrameReadGuard unpins when dropped"]
    pub(super) fn try_read_lock(&self) -> Option<FrameReadGuard<'a>> {
        let guard_opt = self.frame.inner.try_read();
        match guard_opt {
            Some(guard) => Some(FrameReadGuard { frame: guard }),
            None => None,
        }
    }

    #[must_use = "RAII FrameWriteGuard unpins when dropped"]
    pub(super) fn write_lock(&self) -> FrameWriteGuard<'a> {
        FrameWriteGuard { frame: self.frame.inner.write() }
    }

    #[must_use = "RAII FrameReadGuard unpins when dropped"]
    pub(super) fn try_write_lock(&self) -> Option<FrameWriteGuard<'a>> {
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
