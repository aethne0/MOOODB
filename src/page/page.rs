use xxhash_rust::xxh3;

use crate::{
    define_page_fields,
    page::{ByteOrder, PAGE_HEADER_SIZE, PAGE_SIZE},
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

pub(crate) struct Page<'buffer> {
    page_id: u64,
    raw: &'buffer mut [u8; PAGE_SIZE],
}

impl<'buffer> Page<'buffer> {
    pub(crate) fn from_buffer(page_id: u64, buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self {
            page_id,
            raw: buffer,
        }
    }

    pub(crate) fn initialize(
        &mut self,
        page_id: u64,
        page_type: PageType,
        parent: u64,
        right: u64,
    ) {
        self.set_page_id(page_id);
        self.set_page_type(page_type);
        self.set_parent(parent);
        self.set_right(right);

        self.set_upper(0x40);
        self.set_page_id(page_id);
    }

    #[inline(always)]
    pub(crate) fn read_value<T: Copy + ByteOrder>(&self, offset: usize) -> T {
        unsafe {
            let ptr = self.raw.as_ptr().add(offset).cast::<T>();
            ptr.read_unaligned().from_be()
        }
    }

    #[inline(always)]
    pub(crate) fn write_value<T: Copy + ByteOrder>(&mut self, offset: usize, value: T) {
        unsafe {
            let ptr = self.raw.as_mut_ptr().add(offset).cast::<T>();
            ptr.write_unaligned(value.to_be());
        }
    }

    #[rustfmt::skip]
    define_page_fields! {
        checksum,   u64,        0x00;  // This should be first so we can checksum the rest easily
        page_id,    u64,        0x08;
        page_type,  PageType,   0x10;

        parent,     u64,        0x20;
        right,      u64,        0x28;

        upper,      u16,        0x30;  // pointer to end of slots
        free,       u16,        0x32;  // total (fragmented) free space
        lower,      u16,        0x34;  // pointer to top of values
    } // None should be over 0x40 - header is 64 bytes large

    /// Computes the checksum but does not write it to page - must call set_checksum as well
    pub(crate) fn compute_checksum(&mut self) -> u64 {
        xxh3::xxh3_64(&self.raw[8..]) // 8.. because we dont want to checksum the checksum
    }

    pub(crate) fn free_contig(&self) -> usize {
        (1 + self.lower() - self.upper()) as usize
    }

    pub(crate) fn slot_count(&self) -> u16 {
        debug_assert!(self.upper() >= PAGE_HEADER_SIZE as u16);

        (self.upper() - PAGE_HEADER_SIZE as u16) / size_of::<u16>() as u16
    }

    #[inline(always)]
    pub(crate) fn offset_from_slot(&self, slot_index: u16) -> usize {
        self.read_value(PAGE_HEADER_SIZE + (slot_index as usize) * size_of::<u16>())
    }

    #[inline(always)]
    pub(crate) fn key_at_slot(&self, slot_index: u16) -> Option<&[u8]> {
        if slot_index > self.slot_count() - 1 {
            return None;
        }

        let offset = self.offset_from_slot(slot_index);
        let length = self.read_value::<u16>(offset) as usize;

        let start = offset + size_of::<u16>();
        Some(&self.raw[start..start + length])
    }

    /// Returns slot-index of first element not-less-than the search key (left-most that is GE)
    pub(crate) fn find_key_slot(&self, key: &[u8]) -> SearchResult {
        debug_assert!(key.len() < u16::MAX as usize, "passed search key too large");

        if self.slot_count() == 0 {
            return SearchResult::Right;
        }

        let mut low = 0;
        let mut high = self.slot_count() - 1;

        while low < high {
            let mid = low + (high - low) / 2;
            let mid_key = self
                .key_at_slot(mid)
                .expect("binary search should be within bounds");

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

        if low == self.slot_count() {
            SearchResult::Right
        } else {
            SearchResult::NotFound(low)
        }
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
    Root = 0x3,
    Heap = 0x4,
}

#[rustfmt::skip]
impl ByteOrder for PageType {
    #[inline(always)]
    fn from_be(self) -> Self { self }
    #[inline(always)]
    fn to_be(self) -> Self { self }
}
