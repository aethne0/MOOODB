//! Throwaway in-memory IODoer implementation for manual testing.
//! Delete this file when no longer needed.

use std::{
    collections::HashMap,
    pin::Pin,
    sync::{Arc, Mutex},
};

use crate::{
    io::{IODoer, IOError},
    page::PAGE_SIZE,
};

#[derive(Clone)]
pub(crate) struct MemIO {
    pages: Arc<Mutex<HashMap<u64, Box<[u8; PAGE_SIZE]>>>>,
}

impl MemIO {
    pub(crate) fn new() -> Self {
        Self { pages: Arc::new(Mutex::new(HashMap::new())) }
    }
}

impl IODoer for MemIO {
    fn read<'a>(
        &'a self, page_id: u64, data: &'a mut [u8; PAGE_SIZE],
    ) -> Pin<Box<dyn std::future::Future<Output = Result<(), IOError>> + Send + 'a>> {
        Box::pin(async move {
            let pages = self.pages.lock().unwrap();
            match pages.get(&page_id) {
                Some(buf) => {
                    data.copy_from_slice(buf.as_ref());
                    tracing::trace!("[MemIO] read  page_id={page_id} -> {} bytes (hit)", PAGE_SIZE);
                    Ok(())
                }
                None => {
                    data.fill(0);
                    tracing::trace!("[MemIO] read  page_id={page_id} -> zeroed (miss)");
                    Ok(())
                }
            }
        })
    }

    fn write<'a>(
        &'a self, page_id: u64, data: &'a [u8; PAGE_SIZE],
    ) -> Pin<Box<dyn std::future::Future<Output = Result<(), IOError>> + Send + 'a>> {
        Box::pin(async move {
            let mut pages = self.pages.lock().unwrap();
            let buf = pages.entry(page_id).or_insert_with(|| Box::new([0u8; PAGE_SIZE]));
            buf.copy_from_slice(data);

            tracing::trace!("[MemIO] write page_id={page_id} -> {} bytes", PAGE_SIZE);
            Ok(())
        })
    }
}
