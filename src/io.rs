use std::pin::Pin;

use crate::page::PAGE_SIZE;

pub type IOError = Box<dyn std::error::Error + Send + Sync>;

// will be expanded later
pub trait IODoer: Send + Sync {
    fn read<'a>(
        &'a self, page_id: u64, data: &'a mut [u8; PAGE_SIZE],
    ) -> Pin<Box<dyn std::future::Future<Output = Result<(), IOError>> + Send + 'a>>;

    fn write<'a>(
        &'a self, page_id: u64, data: &'a [u8; PAGE_SIZE],
    ) -> Pin<Box<dyn std::future::Future<Output = Result<(), IOError>> + Send + 'a>>;
}
