use std::{
    cell::Cell,
    sync::atomic::{AtomicI16, AtomicU8, AtomicU64, Ordering},
};

use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::{buffer::page_buffer::PageBuffer, io, page::PAGE_SIZE};

#[repr(align(64))]
pub(crate) struct Frame {
    frame_id: usize,
    pub(crate) usage: AtomicU8,
    pub(crate) pins: AtomicI16,
    pub(crate) inner: RwLock<FrameInner>,
}

impl Frame {
    pub(crate) fn new(frame_id: usize) -> Self {
        Self {
            frame_id,
            usage: AtomicU8::new(0),
            pins: AtomicI16::new(0),
            inner: RwLock::new(FrameInner { page_id: 0, dirty: false, buffer: [0; PAGE_SIZE], io_err: None }),
        }
    }

    pub(crate) fn frame_id(&self) -> usize {
        self.frame_id
    }
}

impl<'a> Frame {
    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(crate) fn pin(&'a self, pager: &'a PageBuffer) -> FrameRef<'a> {
        self.pins.fetch_add(1, Ordering::Release);
        FrameRef { frame: self, pager }
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

static THREAD_TOKEN_PREFIX_NEXT: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static THREAD_TOKEN_PREFIX: u64 = THREAD_TOKEN_PREFIX_NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    static THREAD_TOKEN_NEXT: Cell<u64> = Cell::new(0);
}

fn next_token() -> u64 {
    THREAD_TOKEN_PREFIX.with(|&token_prefix| {
        debug_assert!(token_prefix < 0x100, "Only 8 bits allocated for thread token prefix id (max 256 threads)");
        THREAD_TOKEN_NEXT.with(|token_next_cell| {
            let token_next = token_next_cell.get();
            token_next_cell.set(token_next + 1);
            (token_prefix << 56) | (token_next & 0x00ff_ffff_ffff_ffff)
        })
    })
}

/// RAII Ref to a frame - decrements frame pin counter on [`Drop`]
pub(crate) struct FrameRef<'a> {
    frame: &'a Frame,
    pager: &'a PageBuffer,
}

impl<'a> Drop for FrameRef<'a> {
    fn drop(&mut self) {
        self.frame.pins.fetch_sub(1, Ordering::Release);
    }
}

struct FrameReadGuard<'a> {
    frame: &'a RwLockReadGuard<'a, FrameInner>,
    pager: &'a PageBuffer,
}

impl<'a> std::ops::Deref for FrameReadGuard<'a> {
    type Target = RwLockReadGuard<'a, FrameInner>;

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl<'a> FrameReadGuard<'a> {
    /// # SAFETY
    /// Caller must hold a **read** lock on the frame containing `buf` until
    /// the corresponding `token` is returned by [`reap`].
    pub(crate) unsafe fn submit_write(&self, page_id: u64) -> u64 {
        let token = next_token();
        unsafe { self.pager.io.submit_write(token, page_id, &self.frame.buffer) };
        token
    }
}

struct FrameWriteGuard<'a> {
    frame: &'a mut RwLockWriteGuard<'a, FrameInner>,
    pager: &'a PageBuffer,
}

impl<'a> std::ops::Deref for FrameWriteGuard<'a> {
    type Target = RwLockWriteGuard<'a, FrameInner>;

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl<'a> FrameWriteGuard<'a> {
    /// # SAFETY
    /// Caller must hold a **write** lock on the frame containing `buf` until
    /// the corresponding `token` is returned by [`reap`].
    pub(crate) unsafe fn submit_read(&mut self, page_id: u64) -> u64 {
        let token = next_token();
        unsafe { self.pager.io.submit_read(token, page_id, &mut self.frame.buffer) };
        token
    }
}
