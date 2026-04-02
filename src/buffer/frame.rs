use std::sync::atomic::AtomicIsize;

use crate::{io, page::PAGE_SIZE};

#[repr(align(64))]
pub(crate) struct Frame {
    pub(crate) pins: AtomicIsize,
    frame_id: usize,
    pub(crate) inner: tokio::sync::RwLock<FrameInner>,
}

impl Frame {

    pub(crate) fn new(frame_id: usize) -> Self {
        Self {
            frame_id,
            pins: AtomicIsize::new(0),
            inner: tokio::sync::RwLock::new(FrameInner {
                header: FrameHeader { page_id: 0, dirty: false },
                buffer: [0; PAGE_SIZE],
                io_err: None,
            }),
        }
    }

    pub(crate) fn frame_id(&self) -> usize {
        self.frame_id
    }
}

pub(crate) struct FrameHeader {
    pub(crate) page_id: u64,
    pub(crate) dirty: bool,
}

pub(crate) struct FrameInner {
    pub(crate) header: FrameHeader,
    pub(crate) buffer: [u8; PAGE_SIZE],
    /// This is for the loading-in task to flag waiting tasks that there was an
    /// IO error - abandon ship!
    pub(crate) io_err: Option<io::IOError>,
}
