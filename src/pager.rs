// In memory for now

use std::{cell::RefCell, sync::atomic::AtomicU64};

use crate::PAGE_SIZE;

const PAGE_CNT: usize = 256;

pub(crate) struct Pager {
    buffer: Box<[RefCell<[u8; PAGE_SIZE]>; PAGE_CNT]>,
}

impl Pager {
    #[must_use]
    pub(crate) fn new() -> Self {
        let slab = vec![0u8; PAGE_CNT * PAGE_SIZE].into_boxed_slice();




        todo!()
    }
}

#[repr(align(64))]
pub(crate) struct Frame<'buffer> {
    buffer: &'buffer mut [u8; PAGE_SIZE],
    pins: AtomicU64,
}

impl<'buffer> Frame<'buffer> {
    #[must_use]
    fn new(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self {
            buffer,
            pins: AtomicU64::new(0),
        }
    }
}
