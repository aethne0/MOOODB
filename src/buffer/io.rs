use crate::page::PAGE_SIZE;

// can be expanded later
pub(crate) trait IODoer {
    type Error;

    async fn read(&self, page_id: u64, data: &mut [u8; PAGE_SIZE]) -> Result<(), Self::Error>;
    async fn write(&self, page_id: u64, data: &[u8; PAGE_SIZE]) -> Result<(), Self::Error>;
}
