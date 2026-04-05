use std::ops::Bound;

use xxhash_rust::xxh3;

use crate::{
    accessors_read, accessors_write,
    page::{END_OF_PAGE, PAGE_HEADER_SIZE, PAGE_SIZE, PageType, RangeExt, SLOT_SIZE},
    page_fields_ro, page_fields_set,
};

/// Base slotted-page layout shared by all page types.
///
/// Generic over its buffer `B` so the same type works for both mutable and
/// read-only access:
/// - `PageCommon<&'b mut [u8; PAGE_SIZE]>` — full read/write access
/// - `PageCommon<&'b [u8; PAGE_SIZE]>` — read-only (aliased as [`PageCommonRef`])
///
/// Read methods are available whenever `B: AsRef<[u8]>`.
/// Write methods are available whenever `B: AsRef<[u8]> + AsMut<[u8]>`.
pub(crate) struct Common<B> {
    pub(crate) raw: B,
}

// constructors

impl<'b> Common<&'b mut [u8; PAGE_SIZE]> {
    pub(crate) fn from_buffer(buffer: &'b mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }
}

impl<'b> Common<&'b [u8; PAGE_SIZE]> {
    pub(crate) fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }
}

// read impl

impl<B: AsRef<[u8]>> Common<B> {
    accessors_read!(u8, u16, u64);

    #[rustfmt::skip]
    page_fields_ro! {
        checksum,   u64, 0x00;
        page_id,    u64, 0x08;
        page_type,  u8,  0x10;
        parent,     u64, 0x20;
        right,      u64, 0x28;
        next_free,  u64, 0x30;
        upper_ptr,  u16, 0x3a;
        lower_ptr,  u16, 0x3c;
        free,       u16, 0x3e;
    }

    pub(crate) fn raw(&self) -> &[u8] {
        self.raw.as_ref()
    }

    pub(crate) fn is_free(&self) -> bool {
        self.page_type() == PageType::Free as u8
    }

    pub(crate) fn free_bytes_contig(&self) -> u16 {
        1 + self.lower_ptr() - self.upper_ptr()
    }

    pub(crate) fn len(&self) -> u16 {
        assert!(self.upper_ptr() >= PAGE_HEADER_SIZE as u16);
        (self.upper_ptr() - PAGE_HEADER_SIZE) / SLOT_SIZE
    }

    pub(crate) fn offset_from_slot(&self, slot_index: u16) -> u16 {
        self.read_u16(PAGE_HEADER_SIZE + slot_index * SLOT_SIZE)
    }

    pub(crate) fn has_space_entry(&self, entry_len: u16) -> bool {
        assert!(entry_len + SLOT_SIZE < u16::MAX as u16);
        entry_len + SLOT_SIZE <= self.free()
    }

    pub(crate) fn compute_checksum(&self) -> u64 {
        assert!(!self.is_free());
        xxh3::xxh3_64(&self.raw.as_ref()[8..])
    }

    fn slots_range(&self) -> (Bound<usize>, Bound<usize>) {
        let start = PAGE_HEADER_SIZE;
        let end = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
        (start..end).as_usizes()
    }
}

// write impl

impl<B: AsRef<[u8]> + AsMut<[u8]>> Common<B> {
    accessors_write!(u8, u16, u64);

    #[rustfmt::skip]
    page_fields_set! {
        checksum,   u64, 0x00;
        page_id,    u64, 0x08;
        page_type,  u8,  0x10;
        parent,     u64, 0x20;
        right,      u64, 0x28;
        next_free,  u64, 0x30;
        upper_ptr,  u16, 0x3a;
        lower_ptr,  u16, 0x3c;
        free,       u16, 0x3e;
    }

    pub(crate) fn raw_mut(&mut self) -> &mut [u8] {
        self.raw.as_mut()
    }

    pub(crate) fn write_slot(&mut self, slot_index: u16, value: u16) {
        let offset = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
        self.write_u16(offset, value);
    }

    pub(crate) fn initialize_header(&mut self, page_id: u64, page_type: PageType, parent: u64, right: u64) {
        self.set_page_id(page_id);
        self.set_page_type(page_type as u8);
        self.set_parent(parent);
        self.set_right(right);
        self.clear_entries();
    }

    pub(crate) fn clear_entries(&mut self) {
        self.set_upper_ptr(PAGE_HEADER_SIZE);
        self.set_lower_ptr(END_OF_PAGE);
        self.set_free(self.free_bytes_contig());
    }

    pub(crate) fn prepare_insert(&mut self, slot_index: u16, entry_len: u16) -> Option<u16> {
        if !self.has_space_entry(entry_len) {
            return None;
        }

        let offset = self.lower_ptr() - entry_len + 1;

        if slot_index < self.len() {
            let start = PAGE_HEADER_SIZE + slot_index * SLOT_SIZE;
            let end = PAGE_HEADER_SIZE + self.len() * SLOT_SIZE;
            let dest = PAGE_HEADER_SIZE + (slot_index + 1) * SLOT_SIZE;
            self.raw.as_mut().copy_within((start..end).as_usizes(), dest as usize);
        }

        self.write_slot(slot_index, offset);
        self.set_upper_ptr(self.upper_ptr() + SLOT_SIZE);
        self.set_lower_ptr(self.lower_ptr() - entry_len);
        self.set_free(self.free() - SLOT_SIZE - entry_len);

        Some(offset)
    }

    pub(crate) fn delete_slot_at(&mut self, slot_index: u16, entry_len: u16) {
        let slots_range = self.slots_range();
        let start = (slot_index + 1) * SLOT_SIZE;
        let dest = slot_index * SLOT_SIZE;
        self.raw.as_mut()[slots_range].copy_within((start..).as_usizes(), dest as usize);

        self.write_u16(PAGE_HEADER_SIZE + (self.len() - 1) * SLOT_SIZE, 0);
        self.set_upper_ptr(self.upper_ptr() - SLOT_SIZE);
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
        let mut page = Common::from_buffer(&mut buffer);
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
        let mut page = Common::from_buffer(&mut buffer);
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
        let mut page = Common::from_buffer(&mut buffer);
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

    #[test]
    fn test_readonly_view() {
        let mut buffer = [0u8; PAGE_SIZE];
        {
            let mut page = Common::from_buffer(&mut buffer);
            page.initialize_header(7, PageType::Leaf, 0, 0);
        }
        let view = Common::from_buffer_ref(&buffer);
        assert_eq!(view.page_id(), 7);
        assert_eq!(view.page_type(), PageType::Leaf as u8);
        assert!(!view.is_free());
    }
}
