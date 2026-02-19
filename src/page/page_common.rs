use std::ops::Bound;

use xxhash_rust::xxh3;

use crate::{
    accessors,
    page::{PageType, RangeExt, END_OF_PAGE, PAGE_HEADER_SIZE, PAGE_SIZE, SLOT_SIZE},
    page_fields,
};

pub(crate) struct PageCommon<'buffer> {
    pub(crate) raw: &'buffer mut [u8; PAGE_SIZE],
}

impl<'buffer> PageCommon<'buffer> {
    accessors!(u8, u16, u64);

    #[rustfmt::skip]
    page_fields! {
        checksum,   u64,        0x00;  // This should be first so we can checksum the rest easily
        page_id,    u64,        0x08;
        page_type,  u8,         0x10;

        parent,     u64,        0x20;
        right,      u64,        0x28;

        upper_ptr,  u16,        0x3a;  // pointer to end of slots
        lower_ptr,  u16,        0x3c;  // pointer to top of values
        free,       u16,        0x3e;  // total (non-contiguous) free bytes
    } // None should be over 0x40 (PAGE_HEADER_SIZE) - header is 64 bytes large

    pub(crate) fn from_buffer(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }

    // TODO: get rid of these
    #[inline(always)]
    pub(crate) fn raw(&self) -> &[u8; PAGE_SIZE] {
        &*self.raw
    }

    #[inline(always)]
    pub(crate) fn raw_mut(&mut self) -> &mut [u8; PAGE_SIZE] {
        self.raw
    }

    #[inline(always)]
    pub(crate) fn is_free(&self) -> bool {
        self.page_type() == PageType::Free as u8
    }

    #[inline(always)]
    fn slots_range(&self) -> (Bound<usize>, Bound<usize>) {
        let start = PAGE_HEADER_SIZE;
        let end = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
        (start..end).as_usizes()
    }

    /// Does NOT affect free field
    #[inline(always)]
    fn increment_slot_ptr(&mut self) {
        self.set_upper_ptr(self.upper_ptr() + SLOT_SIZE);
    }

    /// Does NOT affect free field
    #[inline(always)]
    fn decrement_slot_ptr(&mut self) {
        self.set_upper_ptr(self.upper_ptr() - SLOT_SIZE);
    }

    pub(crate) fn initialize_header(
        &mut self,
        page_id: u64,
        page_type: PageType,
        parent: u64,
        right: u64,
    ) {
        self.set_page_id(page_id);
        self.set_page_type(page_type as u8);
        self.set_parent(parent);
        self.set_right(right);
        self.clear_entries();
    }

    /// Computes the checksum but does not write it to page - must call set_checksum as well
    pub(crate) fn compute_checksum(&mut self) -> u64 {
        assert!(!self.is_free());
        xxh3::xxh3_64(&self.raw[8..]) // 8.. because we dont want to checksum the checksum
    }

    pub(crate) fn free_bytes_contig(&self) -> u16 {
        1 + self.lower_ptr() - self.upper_ptr()
    }

    #[inline(always)]
    pub(crate) fn len(&self) -> u16 {
        assert!(self.upper_ptr() >= PAGE_HEADER_SIZE as u16);
        (self.upper_ptr() - PAGE_HEADER_SIZE) / SLOT_SIZE
    }

    #[inline(always)]
    pub(crate) fn write_slot(&mut self, slot_index: u16, value: u16) {
        let offset = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
        self.write_u16(offset, value);
    }

    #[inline(always)]
    pub(crate) fn offset_from_slot(&self, slot_index: u16) -> u16 {
        self.read_u16(PAGE_HEADER_SIZE + slot_index * SLOT_SIZE)
    }

    pub(crate) fn clear_entries(&mut self) {
        self.set_upper_ptr(PAGE_HEADER_SIZE);
        self.set_lower_ptr(END_OF_PAGE);
        self.set_free(self.free_bytes_contig());
    }

    #[inline(always)]
    pub(crate) fn has_space_entry(&self, entry_len: u16) -> bool {
        assert!(entry_len + SLOT_SIZE < u16::MAX as u16);
        entry_len + SLOT_SIZE <= self.free()
    }

    /// Prepares an insert at the given slot index. Returns the byte offset at which to write the
    /// entry, or None if there isn't enough space. Caller must compact and retry if needed.
    pub(crate) fn prepare_insert(&mut self, slot_index: u16, entry_len: u16) -> Option<u16> {
        if !self.has_space_entry(entry_len) {
            return None;
        }

        let offset = self.lower_ptr() - entry_len + 1; // This is where the entry will be written

        if slot_index < self.len() {
            let start = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
            let end = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
            let dest = PAGE_HEADER_SIZE + (slot_index + 1) * SLOT_SIZE;
            self.raw
                .copy_within((start..end).as_usizes(), dest as usize);
        }

        self.write_slot(slot_index, offset);
        self.increment_slot_ptr();
        self.set_lower_ptr(self.lower_ptr() - entry_len);
        self.set_free(self.free() - SLOT_SIZE - entry_len);

        Some(offset)
    }

    pub(crate) fn delete_slot_at(&mut self, slot_index: u16, entry_len: u16) {
        dbg!(slot_index, entry_len);
        let slots_range = self.slots_range();
        let start = (slot_index + 1) * SLOT_SIZE;
        let dest = slot_index * SLOT_SIZE;
        dbg!(&slots_range, start, dest);
        self.raw[slots_range].copy_within((start..).as_usizes(), dest as usize);

        self.write_u16(PAGE_HEADER_SIZE + (self.len() - 1) * SLOT_SIZE, 0);
        self.decrement_slot_ptr();
        self.set_free(self.free() + SLOT_SIZE + entry_len);
    }
}

// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initialize_header() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageCommon::from_buffer(&mut buffer);
        page.initialize_header(42, PageType::Heap, 1, 2);

        assert_eq!(page.page_id(), 42);
        assert_eq!(page.page_type(), PageType::Heap as u8);
        assert_eq!(page.parent(), 1);
        assert_eq!(page.right(), 2);
        assert_eq!(page.upper_ptr(), PAGE_HEADER_SIZE as u16);
        assert_eq!(page.lower_ptr(), END_OF_PAGE);
        assert_eq!(page.len(), 0);
        assert!(!page.is_free());
    }

    #[test]
    fn test_checksum() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageCommon::from_buffer(&mut buffer);
        page.initialize_header(42, PageType::Heap, 1, 2);

        let checksum = page.compute_checksum();
        page.set_checksum(checksum);
        assert_eq!(page.checksum(), checksum);

        page.set_page_id(43);
        let new_checksum = page.compute_checksum();
        assert_ne!(checksum, new_checksum);
    }

    #[test]
    fn test_space_and_pointers() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageCommon::from_buffer(&mut buffer);
        page.initialize_header(1, PageType::Heap, 0, 0);

        let initial_free = page.free();
        let contig = page.free_bytes_contig();
        assert_eq!(initial_free, contig);

        let entry_len = 10;
        let off = page.prepare_insert(0, entry_len).unwrap();

        assert_eq!(page.free(), initial_free - entry_len - SLOT_SIZE);
        assert_eq!(page.free_bytes_contig(), contig - entry_len - SLOT_SIZE);
        assert_eq!(page.upper_ptr(), PAGE_HEADER_SIZE as u16 + SLOT_SIZE);
        assert_eq!(page.lower_ptr(), PAGE_SIZE as u16 - 1 - entry_len);
        assert_eq!(off as u16, page.lower_ptr() + 1);
    }
}
