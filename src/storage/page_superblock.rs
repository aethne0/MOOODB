use zerocopy::big_endian;

use super::page_base::PagePrefix;

#[derive(
    Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable, zerocopy::KnownLayout,
)]
#[repr(C)]
pub(super) struct SuperblockHeader {
    pub(super) prefix: PagePrefix,

    pub(super) version: big_endian::U64,

    pub(super) alloc_free_head_id: big_endian::U64,
    pub(super) alloc_bump_next_id: big_endian::U64,

    pub(super) catalog_head_id: big_endian::U64,

    pub(super) page_size: big_endian::U16,

    pub(super) _pad: [u8; 62],
}

impl std::ops::Deref for SuperblockHeader {
    type Target = PagePrefix;
    fn deref(&self) -> &PagePrefix {
        &self.prefix
    }
}
impl std::ops::DerefMut for SuperblockHeader {
    fn deref_mut(&mut self) -> &mut PagePrefix {
        &mut self.prefix
    }
}
