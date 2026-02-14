use xxhash_rust::xxh3;

use crate::{
    accessors,
    page::{PAGE_HEADER_SIZE, PAGE_SIZE},
    page_fields,
};

// NOTE: terminology used
// SLOT: 	The ptr in the slot array that points to the start of an entry.
// ENTRY: 	The actual raw data part of an entry - the keylen+key+vallen+value.
// KEY/VAL: The parsed []byte of key and value, can be read with no further logic.
// OFFSET:  This means literally how many bytes into the page - starts at 0, which is the beginning of the header.
// 		    Usually well oinly care about values from headerSize onwars (0x40..)
// INDEX:   Index is a logical index - so slot-2 would be 4bytes after the end of the header
//		    Similarly, entry-3 could be essentially anywhere on the page (we'd have to check with slot-3)
// Example: SlotIndexToEntryOffset
//          This takes a slot index and tells you its corresponding entries actual
//		    starting address (byte offset) on the page

// NOTE: Slots will point to the entries in key-sorted order. Entries are written in insertion order.
// 		 At the time of insertion slots will be rearranged to keep the keys given from iterating through
// 	 	 Slots ordered (iterating through slots 0..n will return entries in key-order)
//
// Entries are of the format:
// [key_len_u16]:[key_bytes]:[val_len_u16]:[val_bytes]

const SLOT_SIZE: u16 = 2;

pub(crate) struct Page<'buffer> {
    raw: &'buffer mut [u8; PAGE_SIZE],
}

impl<'buffer> Page<'buffer> {
    accessors!(u8, u16, u64);

    #[rustfmt::skip]
    page_fields! {
        checksum,   u64,        0x00;  // This should be first so we can checksum the rest easily
        page_id,    u64,        0x08;
        page_type,  u8,         0x10;

        parent,     u64,        0x20;
        right,      u64,        0x28;

        upper_ptr,  u16,        0x30;  // pointer to end of slots
        lower_ptr,  u16,        0x32;  // pointer to top of values
        free,       u16,        0x34;  // total (non-contiguous) free bytes
    } // None should be over 0x40 - header is 64 bytes large

    /// This creates a page out of an existing buffer, which only involves setting the raw
    /// fat-pointer to the buffer.
    pub(crate) fn from_buffer(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }

    pub(crate) fn new_with_buffer(
        buffer: &'buffer mut [u8; PAGE_SIZE],
        page_id: u64,
        page_type: PageType,
        parent: u64,
        right: u64,
    ) -> Self {
        let mut page = Self { raw: buffer };
        page.initialize(page_id, page_type, parent, right);
        page
    }

    pub(crate) fn initialize(
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

        self.clear()
    }

    #[cfg(debug_assertions)]
    pub(crate) fn get_raw(&self) -> &[u8; PAGE_SIZE] {
        return self.raw;
    }

    /// Computes the checksum but does not write it to page - must call set_checksum as well
    pub(crate) fn compute_checksum(&mut self) -> u64 {
        assert!(!self.is_free());
        xxh3::xxh3_64(&self.raw[8..]) // 8.. because we dont want to checksum the checksum
    }

    pub(crate) fn free_bytes_contig(&self) -> u16 {
        1 + self.lower_ptr() - self.upper_ptr()
    }

    pub(crate) fn len(&self) -> u16 {
        assert!(self.upper_ptr() >= PAGE_HEADER_SIZE as u16);

        (self.upper_ptr() - PAGE_HEADER_SIZE as u16) / size_of::<u16>() as u16
    }

    pub(crate) fn is_leaf(&self) -> bool {
        self.page_type() == PageType::Leaf as u8
    }

    pub(crate) fn is_inner(&self) -> bool {
        self.page_type() == PageType::Inner as u8
    }

    pub(crate) fn is_free(&self) -> bool {
        self.page_type() == PageType::Free as u8
    }

    pub(crate) fn is_heap(&self) -> bool {
        self.page_type() == PageType::Heap as u8
    }

    #[inline(always)]
    fn write_slot(&mut self, slot_index: u16, value: u16) {
        let offset = PAGE_HEADER_SIZE + slot_index as usize * size_of::<u16>();
        self.write_u16(offset, value);
    }

    #[inline(always)]
    fn offset_from_slot(&self, slot_index: u16) -> usize {
        self.read_u16(PAGE_HEADER_SIZE + (slot_index as usize) * size_of::<u16>()) as usize
    }

    fn key_at_slot(&self, slot_index: u16) -> &[u8] {
        assert!(!self.is_free());
        assert!(slot_index < self.len());

        let offset = self.offset_from_slot(slot_index);
        let length = self.read_u16(offset) as usize;

        let start = offset + size_of::<u16>();
        &self.raw[start..start + length]
    }

    fn key_val_at_slot(&self, slot_index: u16) -> (&[u8], &[u8]) {
        assert!(!self.is_free());
        assert!(slot_index < self.len());

        let offset = self.offset_from_slot(slot_index);
        let key_len = self.read_u16(offset) as usize;
        let key_start = offset + size_of::<u16>();

        let val_len = self.read_u16(key_start + key_len) as usize;
        let val_start = key_start + key_len + size_of::<u16>();

        (
            &self.raw[key_start..key_start + key_len],
            &self.raw[val_start..val_start + val_len],
        )
    }

    /// Returns slot-index of first element not-less-than the search key (left-most that is GE)
    fn find_key_slot(&self, key: &[u8]) -> SearchResult {
        assert!(self.is_inner() || self.is_leaf());
        assert!(key.len() < u16::MAX as usize, "passed search key too large");

        if self.len() == 0 {
            return SearchResult::Right;
        }

        let mut low = 0;
        let mut high = self.len();

        while low < high {
            let mid = low + (high - low) / 2;
            let mid_key = self.key_at_slot(mid);

            match mid_key.cmp(key) {
                std::cmp::Ordering::Equal => {
                    return SearchResult::Found(mid);
                }
                std::cmp::Ordering::Less => {
                    low = mid + 1;
                }
                std::cmp::Ordering::Greater => {
                    high = mid;
                }
            }
        }

        if low == self.len() {
            SearchResult::Right
        } else {
            SearchResult::NotFound(low)
        }
    }

    #[inline(always)]
    fn slot_array(&self) -> &[u16] {
        let slot_cnt = self.len() as usize;
        unsafe {
            let bytes = &self.raw[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + size_of::<u16>() * slot_cnt];
            std::slice::from_raw_parts(bytes.as_ptr() as *const u16, bytes.len() / 2)
        }
    }

    #[inline(always)]
    fn slot_array_mut(&mut self, reserve: usize) -> &mut [u16] {
        let slot_cnt = self.len() as usize;
        unsafe {
            let bytes =
                &mut self.raw[PAGE_HEADER_SIZE..PAGE_HEADER_SIZE + size_of::<u16>() * slot_cnt];
            std::slice::from_raw_parts_mut(bytes.as_ptr() as *mut u16, reserve + bytes.len() / 2)
        }
    }

    fn clear(&mut self) {
        assert!(!self.is_free());
        self.set_upper_ptr(PAGE_HEADER_SIZE as u16);
        self.set_lower_ptr(PAGE_SIZE as u16 - 1);
        self.set_free(self.free_bytes_contig());
    }

    pub(crate) fn compact(&mut self) {
        assert!(!self.is_free());

        // clone page to stack-allocated scratch space
        let mut cloned_raw = self.raw.clone();
        let cloned_page = Page::from_buffer(&mut cloned_raw);

        self.clear();

        for (k, v) in cloned_page.iter() {
            // These are already sorted - this maintains sorted order and avoids another
            // binary search per insertion.
            self.insert_unordered(k, v);
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> PageIterator<'a> {
        assert!(!self.is_free());
        PageIterator {
            page: self,
            slot_index: 0,
        }
    }

    pub(crate) fn get(&self, key: &[u8]) -> Option<&[u8]> {
        assert!(!self.is_free());

        match self.find_key_slot(key) {
            SearchResult::Found(slot_index) => Some(self.key_val_at_slot(slot_index).1),
            _ => None,
        }
    }

    pub(crate) fn delete(&mut self, key: &[u8]) {
        assert!(!self.is_free());

        if let SearchResult::Found(slot_index) = self.find_key_slot(key) {
            // delete slot index, recompact slot array, adjust upper pointer, adjust free counter

            let (k, v) = self.key_val_at_slot(slot_index);
            let entry_len = k.len() + v.len() + 2 * size_of::<u16>();

            let slots = self.slot_array_mut(0);
            slots.copy_within(1 + slot_index as usize.., slot_index as usize);
            *slots.last_mut().unwrap() = 0; // zero the (now) trailing slot

            self.set_upper_ptr(self.upper_ptr() - size_of::<u16>() as u16);
            // +Slot +Entry
            self.set_free(self.free() + size_of::<u16>() as u16 + entry_len as u16);
        }
    }

    fn has_space(&self, key: &[u8], val: &[u8]) -> Result<u16, ()> {
        let entry_len = size_of::<u16>() * 2 + val.len() + key.len();
        assert!((entry_len + SLOT_SIZE as usize) < (u16::MAX as usize));
        let entry_len = entry_len as u16;
        if entry_len + SLOT_SIZE > self.free() {
            return Err(());
        }
        Ok(entry_len)
    }

    fn insert_at_slot(&mut self, entry_len: u16, slot_index: u16, key: &[u8], val: &[u8]) {
        // If we don't have enough contiguous free space, but we know we have enough free
        // space overall, then we will perform a compaction
        if self.free_bytes_contig() < (entry_len + SLOT_SIZE)
            && self.free() >= (entry_len + SLOT_SIZE)
        {
            self.compact();
        }

        let mut offset = (self.lower_ptr() - entry_len + 1) as usize;
        self.write_slot(slot_index, offset as u16);

        // write actual entry
        self.write_u16(offset as usize, key.len() as u16);
        offset += size_of::<u16>();
        self.raw[offset..offset + key.len()].copy_from_slice(key);
        offset += key.len();
        self.write_u16(offset as usize, val.len() as u16);
        offset += size_of::<u16>();
        self.raw[offset..offset + val.len()].copy_from_slice(val);

        self.set_upper_ptr(self.upper_ptr() + SLOT_SIZE);
        self.set_lower_ptr(self.lower_ptr() - entry_len);
        self.set_free(self.free() - entry_len - SLOT_SIZE);
    }

    /// Returns whether or not there was enough space.
    /// If there was not then no changes were made.
    pub(crate) fn insert(&mut self, key: &[u8], val: &[u8]) -> bool {
        assert!(self.is_inner() || self.is_leaf());

        let entry_len = match self.has_space(key, val) {
            Err(_) => {
                return false;
            }
            Ok(entry_len) => entry_len,
        };

        // from here forward we know we have enough space in our free segment to insert

        let slot_index = match self.find_key_slot(key) {
            SearchResult::Found(slot_index) | SearchResult::NotFound(slot_index) => {
                let slots = self.slot_array_mut(1);
                slots.copy_within(
                    slot_index as usize..slots.len() - 1,
                    slot_index as usize + 1,
                );
                slot_index
            }
            _ => self.len(), // we are after all existing entries, so append
        };

        self.insert_at_slot(entry_len, slot_index, key, val);
        true
    }

    /// Inserts by appending to end of slot list - used for heap pages.
    pub(crate) fn insert_unordered(&mut self, key: &[u8], val: &[u8]) -> bool {
        assert!(!self.is_free());

        let entry_len = match self.has_space(key, val) {
            Err(_) => {
                return false;
            }
            Ok(entry_len) => entry_len,
        };

        let slot_index = self.len();
        self.insert_at_slot(entry_len, slot_index, key, val);
        true
    }
}

pub(crate) struct PageIterator<'a> {
    page: &'a Page<'a>,
    slot_index: u16,
}

impl<'a> Iterator for PageIterator<'a> {
    type Item = (&'a [u8], &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.slot_index == self.page.len() {
            return None;
        }

        let res = self.page.key_val_at_slot(self.slot_index);
        self.slot_index += 1;
        Some(res)
    }
}

impl<'a> IntoIterator for &'a Page<'a> {
    type Item = (&'a [u8], &'a [u8]);
    type IntoIter = PageIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub(crate) enum SearchResult {
    /// Found an exact match
    Found(u16),
    /// Did not find an exact match, but this is the first element not-less-than the key
    NotFound(u16),
    /// All elements are less than the key - sought-key is to the right of the contents of this page.
    /// This can happen if theres no entries, as well.
    Right,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PageType {
    Free = 0x0,
    Leaf = 0x1,
    Inner = 0x2,
    Heap = 0x3,
}
