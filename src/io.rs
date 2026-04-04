use crate::page::PAGE_SIZE;

pub type IOError = Box<dyn std::error::Error + Send + Sync>;

pub trait IODoer: Send + Sync {
    /// Enqueue a read of `page_id` into `buf`. Returns immediately.
    ///
    /// # SAFETY
    /// Caller must hold a **write** lock on the frame containing `buf` until
    /// the corresponding `token` is returned by [`reap`].
    unsafe fn submit_read(&self, token: u64, page_id: u64, buf: &mut [u8; PAGE_SIZE]);

    /// Enqueue a write of `buf` to `page_id`. Returns immediately.
    ///
    /// # SAFETY
    /// Caller must hold a **read** lock on the frame containing `buf` until
    /// the corresponding `token` is returned by [`reap`].
    unsafe fn submit_write(&self, token: u64, page_id: u64, buf: &[u8; PAGE_SIZE]);

    /// Flush pending submissions to the kernel.
    /// No-op for sync backends and io_uring SQPOLL mode.
    fn flush(&self) {}

    /// Collect completions into `out`. Blocks until at least `min` are ready.
    /// Pass `min = 0` for a non-blocking peek.
    ///
    /// The frame lock must be held until the corresponding token appears here.
    fn reap(&self, min: usize, out: &mut Vec<(u64, Result<(), IOError>)>);
}
