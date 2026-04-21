use std::ops::Bound;
use std::ops::RangeBounds;

use super::serialization::Serialized;
use super::serialization::SerializedU16;
use super::serialization::SerializedU32;
use super::serialization::SerializedU64;
use super::PAGE_SIZE;

// we have some placeholder IDs to mean different things
// These will start at u64::MAX and count down
// its impossible for us to get to these page-ids anyway, due to
// 1. 48/57 bit virtual-addresing
// 2. some number of our bits are taken up by the page size (12 bits lost for 4kib pages)
pub(super) const PAGE_HEADER_SIZE: u16 = 0x20;
pub(super) const SLOT_SIZE: u16 = 2 * size_of::<u16>() as u16;
pub(super) const SLOT_IDX_NULL: u16 = u16::MAX;
const END_OF_PAGE: u16 = PAGE_SIZE as u16 - 1;

/// The first 32 bytes of **every** page on disk, regardless of page type.
///
/// The pager and I/O layer can cast any raw page buffer to this type to read or
/// write the common fields (checksum, pgid, tx_id) without knowing which
/// concrete page type lives in the rest of the buffer.
///
/// Layout (all big-endian):
/// ```text
/// offset  0 | checksum   u64
/// offset  8 | pgid       u64
/// offset 16 | tx_id      u64
/// offset 24 | <reserved> u64
/// ```
#[derive(Clone)]
#[repr(C)]
pub(super) struct PagePrefix {
    pub(super) checksum: SerializedU32,
    pub(super) dbg_pad:  [u8; 4],
    pub(super) txid:     SerializedU64,
    pub(super) pgid:     SerializedU64,
}
const _: () = assert!(size_of::<PagePrefix>() == 24);

impl PagePrefix {
    pub(super) fn new(pgid: u64, checksum: u32, tx_id: u64) -> Self {
        Self {
            checksum: checksum.into(),
            dbg_pad:  *b"SUPA",
            pgid:     pgid.into(),
            txid:     tx_id.into(),
        }
    }
}

/// Converts a range whose bounds implement `Into<usize>` into a plain `(Bound<usize>, Bound<usize>)`,
/// making it usable as a slice index on `[u8]` buffers.
pub(super) trait RangeExt<T> {
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

#[repr(C)]
pub(super) struct PageHeader {
    pub(super) prefix:     PagePrefix,
    pub(super) page_flags: SerializedU16,
    pub(super) upper_ptr:  SerializedU16,
    pub(super) free_bytes: SerializedU16,
    pub(super) lower_ptr:  SerializedU16,
}
const _: () = assert!(size_of::<PageHeader>() == PAGE_HEADER_SIZE as usize);

unsafe impl Serialized for PagePrefix {}
unsafe impl Serialized for PageHeader {}

/*
impl std::ops::Deref for PageHeader {
    type Target = PagePrefix;
    fn deref(&self) -> &PagePrefix {
        &self.prefix
    }
}
impl std::ops::DerefMut for PageHeader {
    fn deref_mut(&mut self) -> &mut PagePrefix {
        &mut self.prefix
    }
}
*/

/// Base slotted-page layout shared by all page types.
pub(super) struct BasePage<Buf> {
    pub(super) raw: Buf,
}

// constructors

impl<'buf> BasePage<&'buf mut [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer(buffer: &'buf mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }
}

impl<'b> BasePage<&'b [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }
}

// deref impls for convenient header field access

impl<Buf: AsRef<[u8]>> std::ops::Deref for BasePage<Buf> {
    type Target = PageHeader;
    fn deref(&self) -> &Self::Target {
        PageHeader::ref_from_bytes(&self.raw.as_ref()[..PAGE_HEADER_SIZE as usize])
    }
}

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> std::ops::DerefMut for BasePage<Buf> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        PageHeader::mut_from_bytes(&mut self.raw.as_mut()[..PAGE_HEADER_SIZE as usize])
    }
}

// read impl

impl<Buf: AsRef<[u8]>> BasePage<Buf> {
    pub(super) fn raw(&self) -> &[u8] {
        self.raw.as_ref()
    }

    pub(super) fn free_bytes_contig(&self) -> u16 {
        1 + self.lower_ptr.get() - self.upper_ptr.get()
    }

    pub(super) fn free_bytes(&self) -> u16 {
        self.free_bytes.get()
    }

    pub(super) fn len(&self) -> u16 {
        assert!(self.upper_ptr.get() >= PAGE_HEADER_SIZE);
        (self.upper_ptr.get() - PAGE_HEADER_SIZE) / SLOT_SIZE
    }

    fn read_u16(&self, offset: u16) -> u16 {
        SerializedU16::ref_from_bytes(&self.raw.as_ref()[offset as usize..]).get()
    }

    /// offset, len
    pub(super) fn offset_len_from_slot(&self, slot_index: u16) -> (u16, u16) {
        (
            self.read_u16(PAGE_HEADER_SIZE + slot_index * SLOT_SIZE),
            self.read_u16(size_of::<u16>() as u16 + PAGE_HEADER_SIZE + slot_index * SLOT_SIZE),
        )
    }

    pub(super) fn has_space_entry(&self, entry_len: u16) -> bool {
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
    pub(super) const fn iter(&self) -> SlottedPageIterator<'_, Buf> {
        SlottedPageIterator::new(self)
    }

    /// Returns the value at `slot_index`, or `None` if the index is out of bounds.
    pub(super) fn get_at_slot(&self, slot_index: u16) -> Option<&[u8]> {
        if slot_index >= self.len() {
            return None;
        }
        Some(self.val_at_slot(slot_index))
    }
}

// write impl

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> BasePage<Buf> {
    pub(super) fn raw_mut(&mut self) -> &mut [u8] {
        self.raw.as_mut()
    }

    fn write_u16(&mut self, offset: u16, val: u16) {
        SerializedU16::from(val).write_to_prefix(&mut self.raw.as_mut()[offset as usize..]);
    }

    /// writes just the slot in the slot-array itself, literally just the (offset, len)
    pub(super) fn write_slot(&mut self, slot_index: u16, offset: u16, len: u16) {
        let slot_offset = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
        self.write_u16(slot_offset, offset);
        self.write_u16(slot_offset + size_of::<u16>() as u16, len);
    }

    pub(super) fn clear_entries(&mut self) {
        self.upper_ptr = (PAGE_HEADER_SIZE).into();
        self.lower_ptr = END_OF_PAGE.into();
        let free_contig = 1 + self.lower_ptr.get() - self.upper_ptr.get();
        self.free_bytes = free_contig.into();

        // zero page if debug - for readability
        #[cfg(debug_assertions)]
        self.raw_mut()[(PAGE_HEADER_SIZE as usize)..].fill(0);
    }

    pub(super) fn prepare_insert(&mut self, slot_index: u16, entry_len: u16) -> Option<u16> {
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
    pub(super) fn delete_slot_entry(&mut self, slot_index: u16) {
        assert!(slot_index < self.len());
        let (offset, len) = self.offset_len_from_slot(slot_index);

        let slots_range = self.slots_range();
        let start = (slot_index + 1) * SLOT_SIZE;
        let dest = slot_index * SLOT_SIZE;
        self.raw.as_mut()[slots_range].copy_within((start..).into_usizes(), dest as usize);

        self.upper_ptr = (self.upper_ptr.get() - SLOT_SIZE).into();
        self.free_bytes = (self.free_bytes.get() + SLOT_SIZE + len).into();

        #[cfg(debug_assertions)]
        {
            // zero data if debug
            self.raw.as_mut()[(offset..offset + len).into_usizes()].fill(0);
            let stale_slot = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
            self.raw.as_mut()[(stale_slot..stale_slot + SLOT_SIZE).into_usizes()].fill(0);
        }
    }
}

pub(super) struct SlottedPageIterator<'a, Buf: AsRef<[u8]>> {
    page:       &'a BasePage<Buf>,
    slot_index: u16,
}

impl<'a, Buf: AsRef<[u8]>> SlottedPageIterator<'a, Buf> {
    #[must_use]
    pub(super) const fn new(page: &'a BasePage<Buf>) -> Self {
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
