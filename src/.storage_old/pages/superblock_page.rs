use std::mem::size_of;

use zerocopy::{big_endian, IntoBytes};

use super::PAGE_ID_NULL;

#[derive(Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable, zerocopy::KnownLayout)]
#[repr(C)]
pub(crate) struct SuperblockHeader {
    _checksum: big_endian::U64,
    pub(crate) page_id: big_endian::U64,
    pub(crate) version: big_endian::U64,

    pub(crate) tx_id: big_endian::U64,

    pub(crate) alloc_free_head_id: big_endian::U64,
    pub(crate) alloc_bump_next_id: big_endian::U64,

    pub(crate) catalog_head_id: big_endian::U64,

    pub(crate) page_size: big_endian::U16,
}

impl SuperblockHeader {
    pub(crate) fn clone_header(&self) -> SuperblockHeader {
        self.clone()
    }
}

pub(crate) struct SuperblockPage<Buf> {
    pub(crate) raw: Buf,
}

// constructors

impl<'buf> SuperblockPage<&'buf [u8]> {
    pub(crate) const fn from_buffer_ref(buffer: &'buf [u8]) -> Self {
        Self { raw: buffer }
    }
}

impl<'buf> SuperblockPage<&'buf mut [u8]> {
    pub(crate) const fn from_buffer(buffer: &'buf mut [u8]) -> Self {
        Self { raw: buffer }
    }

    pub(crate) fn new_with_buffer(
        buffer: &'buf mut [u8], page_size: u16, page_id: u64, tx_id: u64, bump_alloc_page_id_start: u64,
    ) -> Self {
        buffer[size_of::<SuperblockHeader>()..].fill(0);

        let mut page = Self::from_buffer(buffer);

        page.page_id = page_id.into();
        page.alloc_free_head_id = PAGE_ID_NULL.into();
        page.alloc_bump_next_id = bump_alloc_page_id_start.into();
        page.page_size = page_size.into();
        page.version = 1u64.into();
        page.tx_id = tx_id.into();

        page
    }

    pub(crate) fn new_with_buffer_from_header(buffer: &'buf mut [u8], header: &SuperblockHeader) -> Self {
        buffer[..size_of::<SuperblockHeader>()].copy_from_slice(header.as_bytes());
        buffer[size_of::<SuperblockHeader>()..].fill(0);
        Self::from_buffer(buffer)
    }
}

// deref impls for convenient header field access

impl<Buf: AsRef<[u8]>> std::ops::Deref for SuperblockPage<Buf> {
    type Target = SuperblockHeader;
    fn deref(&self) -> &Self::Target {
        zerocopy::FromBytes::ref_from_bytes(&self.raw.as_ref()[..size_of::<SuperblockHeader>()])
            .expect("crateblock buffer must be large enough for header")
    }
}

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> std::ops::DerefMut for SuperblockPage<Buf> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        zerocopy::FromBytes::mut_from_bytes(&mut self.raw.as_mut()[..size_of::<SuperblockHeader>()])
            .expect("crateblock buffer must be large enough for header")
    }
}

// other methods

impl<Buf: AsRef<[u8]>> SuperblockPage<Buf> {}
