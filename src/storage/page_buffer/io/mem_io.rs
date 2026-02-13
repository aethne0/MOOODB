#![allow(clippy::all)]

//! llm throwaway in-memory IODoer implementation for manual testing.
//! Delete this file when no longer needed.
//! ill write a less shit version eventually cause this is an atrocity

use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use super::{IODoer, IOFactory};
use crate::PAGE_SIZE;

enum PendingOp {
    Read { token: u64, page_id: u64, buf: *mut [u8] },
    Write { token: u64, page_id: u64, buf: *const [u8] },
}

// SAFETY: the buffer pointers are valid for the duration of the pending queue
// because callers uphold the submit_read/submit_write safety contracts.
unsafe impl Send for PendingOp {}
unsafe impl Sync for PendingOp {}

#[derive(Clone)]
pub(crate) struct MemIO {
    pages: Arc<Mutex<HashMap<u64, Box<[u8]>>>>,
    pending: Arc<Mutex<Vec<PendingOp>>>,
    done: Arc<Mutex<Vec<(u64, Result<(), std::io::ErrorKind>)>>>,
}

impl MemIO {
    pub(crate) fn new() -> Self {
        Self {
            pages: Arc::new(Mutex::new(HashMap::new())),
            pending: Arc::new(Mutex::new(Vec::new())),
            done: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

impl IOFactory for MemIO {
    fn make_io_doer(&self) -> Box<dyn IODoer> {
        // Share the backing page store, but each doer gets its own queues
        // (mirroring per-thread io_uring rings that don't share a CQ/SQ)
        Box::new(MemIO {
            pages: Arc::clone(&self.pages),
            pending: Arc::new(Mutex::new(Vec::new())),
            done: Arc::new(Mutex::new(Vec::new())),
        })
    }
}

impl IODoer for MemIO {
    unsafe fn submit_read(&self, token: u64, page_id: u64, buf: &mut [u8]) {
        self.pending
            .lock()
            .unwrap()
            .push(PendingOp::Read { token, page_id, buf });
    }

    unsafe fn submit_write(&self, token: u64, page_id: u64, buf: &[u8]) {
        self.pending
            .lock()
            .unwrap()
            .push(PendingOp::Write { token, page_id, buf });
    }

    fn flush(&self) {
        let ops: Vec<PendingOp> = self.pending.lock().unwrap().drain(..).collect();
        let mut pages = self.pages.lock().unwrap();
        let mut done = self.done.lock().unwrap();

        for op in ops {
            match op {
                PendingOp::Read { token, page_id, buf } => {
                    // SAFETY: caller holds a write lock on the frame until this
                    // token is returned by reap; the pointer is valid.
                    let buf = unsafe { &mut *buf };
                    match pages.get(&page_id) {
                        Some(src) => buf.copy_from_slice(src.as_ref()),
                        None => buf.fill(0),
                    }
                    tracing::trace!("[MemIO] read  page_id={page_id}");
                    done.push((token, Ok(())));
                }
                PendingOp::Write { token, page_id, buf } => {
                    // SAFETY: caller holds a read lock on the frame until this
                    // token is returned by reap; the pointer is valid.
                    let buf = unsafe { &*buf };
                    pages
                        .entry(page_id)
                        .or_insert_with(|| vec![0u8; PAGE_SIZE as usize].into_boxed_slice())
                        .copy_from_slice(buf);
                    tracing::trace!("[MemIO] write page_id={page_id}");
                    done.push((token, Ok(())));
                }
            }
        }
    }

    fn reap(&self, min: usize, out: &mut Vec<(u64, Result<(), std::io::ErrorKind>)>) {
        assert_ne!(min, 0);
        out.extend(self.done.lock().unwrap().drain(..));
    }

    fn reap_one(&self) -> (u64, Result<(), std::io::ErrorKind>) {
        loop {
            let mut done = self.done.lock().unwrap();
            if !done.is_empty() {
                return done.remove(0);
            }
            drop(done);
            std::thread::yield_now();
        }
    }

    fn peek(&self) -> usize {
        self.done.lock().unwrap().len()
    }
}
