pub(crate) mod mem_io;

pub(crate) trait IOFactory: Send + Sync {
    /// Called once per worker thread to create that thread's dedicated ring.
    fn make_io_doer(&self) -> Box<dyn IODoer>; // TODO probably this will have to take page size or
                                               // something - or maybe not!
}

pub(crate) trait IODoer: Send + Sync {
    /// Enqueue a read of `page_id` into `buf`. Returns immediately.
    ///
    /// # SAFETY
    /// Caller must hold a **write** lock on the frame containing `buf` until
    /// the corresponding `token` is returned by [`reap`].
    unsafe fn submit_read(&self, token: u64, page_id: u64, buf: &mut [u8]);

    /// Enqueue a write of `buf` to `page_id`. Returns immediately.
    ///
    /// # SAFETY
    /// Caller must hold a **read** lock on the frame containing `buf` until
    /// the corresponding `token` is returned by [`reap`].
    unsafe fn submit_write(&self, token: u64, page_id: u64, buf: &[u8]);

    /// Flush pending submissions to the kernel.
    /// No-op for sync backends and io_uring SQPOLL mode.
    fn flush(&self);

    /// Collect completions into `out`. Blocks until at least `min` are ready.
    /// [`min`] must be > 0
    ///
    /// The frame lock must be held until the corresponding token appears here.
    fn reap(&self, min: usize, out: &mut Vec<(u64, Result<(), std::io::ErrorKind>)>);

    /// Collect completions into `out`. Blocks until at least `min` are ready.
    /// [`min`] must be > 0
    ///
    /// The frame lock must be held until the corresponding token appears here.
    fn reap_one(&self) -> (u64, Result<(), std::io::ErrorKind>);

    /// Peek completions - non-blocking
    fn peek(&self) -> usize;
}
