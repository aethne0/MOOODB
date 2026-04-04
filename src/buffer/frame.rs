use std::sync::atomic::AtomicU8;

use parking_lot::RwLock;

use crate::{io, page::PAGE_SIZE};

#[repr(align(64))]
pub(crate) struct Frame {
    frame_id: usize,
    pub(crate) usage: AtomicU8,
    pub(crate) inner: RwLock<FrameInner>,
}

impl Frame {
    pub(crate) fn new(frame_id: usize) -> Self {
        Self {
            frame_id,
            usage: AtomicU8::new(0),
            inner: RwLock::new(FrameInner { page_id: 0, dirty: false, buffer: [0; PAGE_SIZE], io_err: None }),
        }
    }

    pub(crate) fn frame_id(&self) -> usize {
        self.frame_id
    }
}

#[repr(align(64))]
pub(crate) struct FrameInner {
    pub(crate) buffer: [u8; PAGE_SIZE],

    pub(crate) page_id: u64,
    pub(crate) dirty: bool,
    /// This is for the loading-in task to flag waiting tasks that there was an
    /// IO error - abandon ship!
    pub(crate) io_err: Option<io::IOError>,
}
