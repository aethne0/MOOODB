use std::ops::{Bound, RangeBounds};

use xxhash_rust::xxh3;
use zerocopy::big_endian;

// we have some placeholder IDs to mean different things
// These will start at u64::MAX and count down
// its impossible for us to get to these page-ids anyway, due to
// 1. 48/57 bit virtual-addresing
// 2. some number of our bits are taken up by the page size (12 bits lost for 4kib pages)
pub(crate) const PAGE_ID_NULL: u64 = u64::MAX;
pub(crate) const SLOT_SIZE: u16 = 2 * size_of::<u16>() as u16;
pub(crate) const PAGE_HEADER_SIZE: u16 = 0x40;

/// Converts a range whose bounds implement `Into<usize>` into a plain `(Bound<usize>, Bound<usize>)`,
/// making it usable as a slice index on `[u8]` buffers.
pub(crate) trait RangeExt<T> {
    fn into_usizes(self) -> (Bound<usize>, Bound<usize>);
}

impl<T, R> RangeExt<T> for R
where
    T: Into<usize> + Copy,
    R: RangeBounds<T>,
{
    fn into_usizes(self) -> (Bound<usize>, Bound<usize>) {
        let start = match self.start_bound() {
            Bound::Included(&t) => Bound::Included(t.into()),
            Bound::Excluded(&t) => Bound::Excluded(t.into()),
            Bound::Unbounded => Bound::Unbounded,
        };

        let end = match self.end_bound() {
            Bound::Included(&t) => Bound::Included(t.into()),
            Bound::Excluded(&t) => Bound::Excluded(t.into()),
            Bound::Unbounded => Bound::Unbounded,
        };

        (start, end)
    }
}

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable, zerocopy::KnownLayout)]
#[repr(C)]
pub(crate) struct PageHeader {
    _checksum: big_endian::U64,
    pub(crate) page_id: big_endian::U64,
    pub(crate) tx_id: big_endian::U64,

    pub(crate) parent_id: big_endian::U64,
    pub(crate) next_id: big_endian::U64,

    pub(crate) upper_ptr: big_endian::U16,
    pub(crate) lower_ptr: big_endian::U16,
    pub(crate) free_bytes: big_endian::U16,
    pub(crate) page_flags: big_endian::U16,

    _pad: [u8; 16],
}
const _: () = assert!(size_of::<PageHeader>() == PAGE_HEADER_SIZE as usize);

/// Base slotted-page layout shared by all page types.
pub(crate) struct BasePage<Buf> {
    pub(crate) raw: Buf,
}

// constructors

impl<'buf> BasePage<&'buf mut [u8]> {
    pub(crate) const fn from_buffer(buffer: &'buf mut [u8]) -> Self {
        Self { raw: buffer }
    }
}

impl<'b> BasePage<&'b [u8]> {
    pub(crate) const fn from_buffer_ref(buffer: &'b [u8]) -> Self {
        Self { raw: buffer }
    }
}

// deref impls for convenient header field access

impl<Buf: AsRef<[u8]>> std::ops::Deref for BasePage<Buf> {
    type Target = PageHeader;
    fn deref(&self) -> &Self::Target {
        zerocopy::FromBytes::ref_from_bytes(&self.raw.as_ref()[..PAGE_HEADER_SIZE as usize])
            .expect("page buffer must be large enough for header")
    }
}

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> std::ops::DerefMut for BasePage<Buf> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        zerocopy::FromBytes::mut_from_bytes(&mut self.raw.as_mut()[..PAGE_HEADER_SIZE as usize])
            .expect("page buffer must be large enough for header")
    }
}

// read impl

impl<Buf: AsRef<[u8]>> BasePage<Buf> {
    pub(crate) fn raw(&self) -> &[u8] {
        self.raw.as_ref()
    }

    fn end_of_page(&self) -> u16 {
        (self.raw().len() - 1).try_into().unwrap()
    }

    pub(crate) fn free_bytes_contig(&self) -> u16 {
        1 + self.lower_ptr.get() - self.upper_ptr.get()
    }

    pub(crate) fn free_bytes(&self) -> u16 {
        self.free_bytes.get()
    }

    pub(crate) fn len(&self) -> u16 {
        assert!(self.upper_ptr.get() >= PAGE_HEADER_SIZE);
        (self.upper_ptr.get() - PAGE_HEADER_SIZE) / SLOT_SIZE
    }

    pub(crate) fn right(&self) -> u64 {
        self.next_id.get()
    }

    fn read_u16(&self, offset: u16) -> u16 {
        let buf = self.raw.as_ref();
        let idx = offset as usize;
        u16::from_be_bytes([buf[idx], buf[idx + 1]])
    }

    pub(crate) fn offset_len_from_slot(&self, slot_index: u16) -> (u16, u16) {
        (
            self.read_u16(PAGE_HEADER_SIZE + slot_index * SLOT_SIZE),
            self.read_u16(size_of::<u16>() as u16 + PAGE_HEADER_SIZE + slot_index * SLOT_SIZE),
        )
    }

    pub(crate) fn has_space_entry(&self, entry_len: u16) -> bool {
        assert!(entry_len + SLOT_SIZE < u16::MAX);
        entry_len + SLOT_SIZE <= self.free_bytes.get()
    }

    fn slots_range(&self) -> (Bound<usize>, Bound<usize>) {
        let start = PAGE_HEADER_SIZE;
        let end = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
        (start..end).into_usizes()
    }

    fn val_at_slot(&self, slot_index: u16) -> &[u8] {
        assert!(slot_index < self.len());
        let (offset, len) = self.offset_len_from_slot(slot_index);
        &self.raw()[(offset..offset + len).into_usizes()]
    }

    /// Returns an iterator over `(slot_index, value)` pairs in slot order.
    pub(crate) const fn iter(&self) -> SlottedPageIterator<'_, Buf> {
        SlottedPageIterator::new(self)
    }

    /// Returns the value at `slot_index`, or `None` if the index is out of bounds.
    pub(crate) fn get_at_slot(&self, slot_index: u16) -> Option<&[u8]> {
        if slot_index >= self.len() {
            return None;
        }
        Some(self.val_at_slot(slot_index))
    }
}

// write impl

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> BasePage<Buf> {
    pub(crate) fn set_right(&mut self, val: u64) {
        self.next_id = val.into();
    }

    pub(crate) fn raw_mut(&mut self) -> &mut [u8] {
        self.raw.as_mut()
    }

    pub(crate) fn write_slot(&mut self, slot_index: u16, offset: u16, len: u16) {
        let slot_offset = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
        self.write_u16(slot_offset, offset);
        self.write_u16(slot_offset + size_of::<u16>() as u16, len);
    }

    fn write_u16(&mut self, offset: u16, val: u16) {
        let buf = self.raw.as_mut();
        let idx = offset as usize;
        buf[idx..idx + 2].copy_from_slice(&val.to_be_bytes());
    }

    pub(crate) fn initialize_header(&mut self, page_id: u64, parent: u64, right: u64) {
        self.page_id = page_id.into();
        self.parent_id = parent.into();
        self.next_id = right.into();
        self.clear_entries();
    }

    pub(crate) fn clear_entries(&mut self) {
        self.upper_ptr = (PAGE_HEADER_SIZE).into();
        self.lower_ptr = self.end_of_page().into();
        let free_contig = 1 + self.lower_ptr.get() - self.upper_ptr.get();
        self.free_bytes = free_contig.into();
    }

    pub(crate) fn prepare_insert(&mut self, slot_index: u16, entry_len: u16) -> Option<u16> {
        if !self.has_space_entry(entry_len) {
            return None;
        }

        let lower = self.lower_ptr.get();
        let offset = lower - entry_len + 1;

        if slot_index < self.len() {
            let start = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
            let end = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
            let dest = PAGE_HEADER_SIZE + (slot_index + 1) * SLOT_SIZE;
            self.raw.as_mut().copy_within((start..end).into_usizes(), dest as usize);
        }

        self.write_slot(slot_index, offset, entry_len);
        self.upper_ptr = (self.upper_ptr.get() + SLOT_SIZE).into();
        self.lower_ptr = (self.lower_ptr.get() - entry_len).into();
        self.free_bytes = (self.free_bytes.get() - SLOT_SIZE - entry_len).into();

        Some(offset)
    }

    /// Removes the entry at `slot_index`, shifting subsequent slots left.
    /// Does nothing if `slot_index` is out of bounds.
    pub(crate) fn delete_slot_entry(&mut self, slot_index: u16) {
        assert!(slot_index < self.len());
        // offset is unused because we dont touch the actual data (compaction takes care of this)
        let (_offset, len) = self.offset_len_from_slot(slot_index);

        let slots_range = self.slots_range();
        let start = (slot_index + 1) * SLOT_SIZE;
        let dest = slot_index * SLOT_SIZE;
        self.raw.as_mut()[slots_range].copy_within((start..).into_usizes(), dest as usize);

        self.write_u16(PAGE_HEADER_SIZE + (self.len() - 1) * SLOT_SIZE, 0);
        self.upper_ptr = (self.upper_ptr.get() - SLOT_SIZE).into();
        self.free_bytes = (self.free_bytes.get() + SLOT_SIZE + len).into();
    }
}

pub(crate) struct SlottedPageIterator<'a, Buf: AsRef<[u8]>> {
    page: &'a BasePage<Buf>,
    slot_index: u16,
}

impl<'a, Buf: AsRef<[u8]>> SlottedPageIterator<'a, Buf> {
    #[must_use]
    pub(crate) const fn new(page: &'a BasePage<Buf>) -> Self {
        Self { page, slot_index: 0 }
    }
}

impl<'a, B: AsRef<[u8]>> Iterator for SlottedPageIterator<'a, B> {
    type Item = (u16, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.slot_index == self.page.len() {
            return None;
        }

        let slot = self.slot_index;
        let res = self.page.val_at_slot(slot);
        self.slot_index += 1;
        Some((slot, res))
    }
}

impl<'a, B: AsRef<[u8]>> IntoIterator for &'a BasePage<B> {
    type Item = (u16, &'a [u8]);
    type IntoIter = SlottedPageIterator<'a, B>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initialize_header() {
        let mut buffer = [0u8; 4096];
        let mut page = BasePage::from_buffer(&mut buffer);
        page.initialize_header(42, 1, 2);

        assert_eq!(page.page_id.get(), 42);
        assert_eq!(page.parent_id.get(), 1);
        assert_eq!(page.next_id.get(), 2);
        assert_eq!(page.upper_ptr.get(), PAGE_HEADER_SIZE);
        assert_eq!(page.lower_ptr.get(), 4095);
        assert_eq!(page.len(), 0);
    }

    #[test]
    fn test_space_and_pointers() {
        let mut buffer = [0u8; 4096];
        let mut page = BasePage::from_buffer(&mut buffer);
        page.initialize_header(1, 0, 0);

        let initial_free = page.free_bytes();
        let contig = page.free_bytes_contig();
        assert_eq!(initial_free, contig);

        let entry_len = 10;
        let off = page.prepare_insert(0, entry_len).unwrap();

        assert_eq!(page.free_bytes(), initial_free - entry_len - SLOT_SIZE);
        assert_eq!(page.free_bytes_contig(), contig - entry_len - SLOT_SIZE);
        assert_eq!(page.upper_ptr.get(), PAGE_HEADER_SIZE + SLOT_SIZE);
        assert_eq!(page.lower_ptr.get(), 4096 as u16 - 1 - entry_len);
        assert_eq!(off as u16, page.lower_ptr.get() + 1);
    }

    #[test]
    fn test_readonly_view() {
        let mut buffer = [0u8; 4096];
        {
            let mut page = BasePage::from_buffer(&mut buffer);
            page.initialize_header(7, 0, 0);
        }
        let view = BasePage::from_buffer_ref(&buffer);
        assert_eq!(view.page_id.get(), 7);
    }
}
