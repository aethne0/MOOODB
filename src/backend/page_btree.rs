use std::ops::Deref;
use std::ops::DerefMut;

use super::serialization::*;
use super::PAGE_SIZE;
use crate::mooo_assert;

// This line should give us a compile error if we set page-size too low

#[repr(C)]
pub(super) struct BtreePageHeader {
    pub(super) prefix:     PagePrefix,
    _unused:               [u8; 24],
    pub(super) page_type:  SerializedU16,
    /// ptr to byte after end of slot array (grows from top - end of header)
    pub(super) upper_ptr:  SerializedU16,
    pub(super) free_bytes: SerializedU16,
    /// ptr to byte before start of values (grows from bottom)
    pub(super) lower_ptr:  SerializedU16,
}
const _: () = mooo_assert!(size_of::<BtreePageHeader>() == PAGE_HEADER_SIZE as usize);
unsafe impl Serialized for BtreePageHeader {}

const PGTYPE_BTREELF: SerializedU64 = SerializedU64(*b"\0BtreeLf");
const PGTYPE_BTREEIN: SerializedU64 = SerializedU64(*b"\0BtreeIn");

/// A sorted B-tree page storing key-value pairs in ascending key order.
pub(super) struct BtreePage<Buf> {
    raw: Buf,
}

// constructors

// Values are laid out like:
// [key_len:u16][key:var][val:var]
// So val starts at sizeof<u16> + key_len
pub(super) const SLOT_INDEX_NULL: u16 = u16::MAX;
const SLOT_SIZE: u16 = 2 * size_of::<u16>() as u16;
const PAGE_USABLE_SPACE: u16 = PAGE_SIZE as u16 - PAGE_HEADER_SIZE;
const MAX_ENTRY_LEN: usize = ((PAGE_SIZE - PAGE_HEADER_SIZE as usize) / 2) - (SLOT_SIZE as usize);

impl<'buf> BtreePage<&'buf mut [u8; PAGE_SIZE]> {
    pub(super) fn initialize_with_buffer(
        buffer: &'buf mut [u8; PAGE_SIZE], page_type: BtreePageType,
    ) -> Self {
        let mut page = Self { raw: buffer };
        page.clear();
        page.set_page_type(page_type);
        page
    }

    /// Page MUST be initialized
    pub(super) fn from_buffer(buffer: &'buf mut [u8; PAGE_SIZE]) -> Self {
        let page = Self { raw: buffer };
        mooo_assert!(page.is_initialized());
        page
    }
}

impl<'b> BtreePage<&'b [u8; PAGE_SIZE]> {
    /// Page MUST be initialized
    pub(super) fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        let page = Self { raw: buffer };
        mooo_assert!(page.is_initialized());
        page
    }
}

// deref to header

impl<Buf: AsRef<[u8]>> Deref for BtreePage<Buf> {
    type Target = BtreePageHeader;

    fn deref(&self) -> &BtreePageHeader {
        BtreePageHeader::ref_from_bytes(&self.raw.as_ref()[..PAGE_HEADER_SIZE as usize])
    }
}

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> DerefMut for BtreePage<Buf> {
    fn deref_mut(&mut self) -> &mut BtreePageHeader {
        BtreePageHeader::mut_from_bytes(&mut self.raw.as_mut()[..PAGE_HEADER_SIZE as usize])
    }
}

// read impl

#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BtreePageType {
    Inner = 1,
    Leaf = 2,
}

impl<Buf: AsRef<[u8]>> BtreePage<Buf> {
    fn raw(&self) -> &[u8] {
        self.raw.as_ref()
    }

    fn free_bytes_contig(&self) -> u16 {
        mooo_assert!(self.lower_ptr.get() >= self.upper_ptr.get() - 1);
        1 + self.lower_ptr.get() - self.upper_ptr.get()
    }

    /// Assert
    fn is_initialized(&self) -> bool {
        // check that type is set
        let _ = self.get_page_type();
        // check that pointers are (seemingly) sane
        mooo_assert!(self.lower_ptr.get() >= self.upper_ptr.get() - 1);
        mooo_assert!(self.free_bytes_contig() <= self.free_bytes.get());
        true
    }

    pub(super) fn len(&self) -> u16 {
        (self.upper_ptr.get() - PAGE_HEADER_SIZE) / SLOT_SIZE
    }

    fn bytes_used(&self) -> u16 {
        PAGE_USABLE_SPACE - self.free_bytes.get()
    }

    pub(super) fn entry_bytes(&self) -> u16 {
        PAGE_USABLE_SPACE - self.free_bytes.get() - self.len() * SLOT_SIZE
    }

    pub(super) fn is_full_enough(&self) -> bool {
        self.free_bytes.get() <= PAGE_USABLE_SPACE / 2
    }

    pub(super) fn is_full_enough_without_first(&self) -> bool {
        mooo_assert!(self.len() > 0);
        let entry_size = self.len_from_slot(0) as u16;
        self.free_bytes.get() + entry_size <= PAGE_USABLE_SPACE / 2
    }

    pub(super) fn is_full_enough_without_last(&self) -> bool {
        mooo_assert!(self.len() > 0);
        let entry_size = self.len_from_slot(self.len() - 1) as u16 + SLOT_SIZE;
        self.free_bytes.get() + entry_size <= PAGE_USABLE_SPACE / 2
    }

    pub(super) fn could_merge_with<BufOther: AsRef<[u8]>>(
        &self, other: &BtreePage<BufOther>,
    ) -> bool {
        self.bytes_used() + other.bytes_used() <= PAGE_USABLE_SPACE
    }

    pub(super) fn key_val_slices_from_slot(&self, slot_index: u16) -> (&[u8], &[u8]) {
        let entry = self.entry_slice_from_slot(slot_index);
        mooo_assert!(entry.len() > size_of::<SerializedU16>());
        let key_len =
            SerializedU16::read_from_bytes(&entry[0..size_of::<SerializedU16>()]).get() as usize;
        entry[size_of::<SerializedU16>()..].split_at(key_len)
    }

    fn entry_slice_from_slot(&self, slot_index: u16) -> &[u8] {
        mooo_assert!(slot_index < self.len());
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_ref();

        let offset = SerializedU16::ref_from_bytes(&raw[base..]).get() as usize;
        let len = SerializedU16::ref_from_bytes(&raw[base + size_of::<u16>()..]).get() as usize;
        &raw[offset..offset + len]
    }

    fn len_from_slot(&self, slot_index: u16) -> u16 {
        mooo_assert!(slot_index < self.len());
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_ref();
        SerializedU16::ref_from_bytes(&raw[base + size_of::<u16>()..]).get()
    }

    pub(super) fn is_leaf(&self) -> bool {
        self.page_type.get() == BtreePageType::Leaf as u16
    }

    pub(super) fn is_inner(&self) -> bool {
        self.page_type.get() == BtreePageType::Inner as u16
    }

    pub(super) fn get_page_type(&self) -> BtreePageType {
        let t = self.page_type.get();
        if t == BtreePageType::Inner as u16 {
            BtreePageType::Inner
        } else if t == BtreePageType::Leaf as u16 {
            BtreePageType::Leaf
        } else {
            unreachable!("invalid page type")
        }
    }

    /// Binary searches for `key` and returns a [`SearchResult`] indicating whether it was
    /// found and at which slot, or where it would be inserted to maintain order.
    pub(super) fn find_slot_from_key(&self, key: &[u8]) -> SearchResult {
        let _ = u16::try_from(key.len()).expect("passed key too large");

        if self.len() == 0 {
            return SearchResult::Right;
        }

        let mut low = 0;
        let mut high = self.len();

        while low < high {
            let mid = low + (high - low) / 2;
            let (mid_key, _) = self.key_val_slices_from_slot(mid);

            match mid_key.cmp(key) {
                std::cmp::Ordering::Equal => return SearchResult::Found(mid),
                std::cmp::Ordering::Less => low = mid + 1,
                std::cmp::Ordering::Greater => high = mid,
            }
        }

        if low == self.len() {
            SearchResult::Right
        } else {
            SearchResult::NotFound(low)
        }
    }

    /// Returns an iterator over `(key, value)` pairs in ascending key order.
    pub(super) const fn iter(&self) -> SortedIterator<'_, Buf> {
        SortedIterator { page: self, slot_index: 0 }
    }

    /// Returns the value associated with `key`, or `None` if not present.
    pub(super) fn get(&self, key: &[u8]) -> Option<&[u8]> {
        match self.find_slot_from_key(key) {
            SearchResult::Found(slot_index) => Some(self.key_val_slices_from_slot(slot_index).1),
            _ => None,
        }
    }

    /// Returns the child page to follow for `key` during tree traversal.
    ///
    /// Finds the last slot whose key does not exceed `key`. Slot 0 is a catch-all for any key
    /// smaller than slot 1's separator, so inner nodes never need their keys updated during descent.
    pub(super) fn get_traversal_next_page(&self, key: &[u8]) -> Option<(&[u8], u16)> {
        mooo_assert!(self.is_inner(), "shouldnt be called on leaf node");
        mooo_assert!(self.len() > 0, "inner node shouldnt be empty");
        let slot_index = match self.find_slot_from_key(key) {
            SearchResult::Found(slot_index) => slot_index,
            SearchResult::NotFound(slot_index) => slot_index.saturating_sub(1),
            SearchResult::Right => self.len() - 1,
        };
        Some((self.key_val_slices_from_slot(slot_index).1, slot_index))
    }

    fn has_space(&self, key: &[u8], val: &[u8]) -> Result<u16, ()> {
        let entry_len = u16::try_from(size_of::<SerializedU16>() + key.len() + val.len())
            .expect("entry too big for u16");
        if entry_len + SLOT_SIZE > self.free_bytes.get() {
            return Err(());
        }
        Ok(entry_len)
    }
}

// write impl

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> BtreePage<Buf> {
    pub(super) fn key_val_slices_from_slot_mut(
        &mut self, slot_index: u16,
    ) -> (&mut [u8], &mut [u8]) {
        mooo_assert!(slot_index < self.len());
        let entry = self.entry_slices_from_slot_mut(slot_index);
        mooo_assert!(entry.len() > size_of::<SerializedU16>());
        let key_len =
            SerializedU16::read_from_bytes(&entry[0..size_of::<SerializedU16>()]).get() as usize;
        entry[size_of::<SerializedU16>()..].split_at_mut(key_len)
    }

    /// Entire entry slice including value-offset header
    fn entry_slices_from_slot_mut(&mut self, slot_index: u16) -> &mut [u8] {
        mooo_assert!(slot_index < self.len());
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_ref();

        let offset = SerializedU16::ref_from_bytes(&raw[base..]).get() as usize;
        let len = SerializedU16::ref_from_bytes(&raw[base + size_of::<u16>()..]).get() as usize;
        &mut self.raw.as_mut()[offset..offset + len]
    }

    fn write_slot(&mut self, slot_index: u16, offset: u16, len: u16) {
        mooo_assert!(
            slot_index <= self.len(),
            "we shouldnt be writing past the next available slot"
        );
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_mut();
        SerializedU16::from(offset).write_to_prefix(&mut raw[base..]);
        SerializedU16::from(len).write_to_prefix(&mut raw[base + size_of::<u16>()..]);
    }

    pub(super) fn clear(&mut self) {
        self.upper_ptr = PAGE_HEADER_SIZE.into();
        self.lower_ptr = END_OF_PAGE.into();
        self.free_bytes = PAGE_USABLE_SPACE.into();
        #[cfg(debug_assertions)]
        self.raw.as_mut()[PAGE_HEADER_SIZE as usize..].fill(0);
    }

    fn prepare_insert(&mut self, slot_index: u16, entry_len: u16) -> Option<u16> {
        if entry_len + SLOT_SIZE > self.free_bytes.get() {
            return None;
        }

        let lower = self.lower_ptr.get();
        let offset = lower - entry_len + 1;

        if slot_index < self.len() {
            let start = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
            let end = (PAGE_HEADER_SIZE + self.len() * SLOT_SIZE) as usize;
            let dest = start + SLOT_SIZE as usize;
            self.raw.as_mut().copy_within(start..end, dest);
        }

        self.write_slot(slot_index, offset, entry_len);
        self.upper_ptr = (self.upper_ptr.get() + SLOT_SIZE).into();
        self.lower_ptr = (lower - entry_len).into();
        self.free_bytes = (self.free_bytes.get() - SLOT_SIZE - entry_len).into();

        Some(offset)
    }

    pub(super) fn delete_slot_entry(&mut self, slot_index: u16) {
        mooo_assert!(slot_index < self.len());
        let len = self.len_from_slot(slot_index);
        let del = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let end = (PAGE_HEADER_SIZE + self.len() * SLOT_SIZE) as usize;
        self.raw.as_mut().copy_within(del + SLOT_SIZE as usize..end, del);

        self.upper_ptr = (self.upper_ptr.get() - SLOT_SIZE).into();
        self.free_bytes = (self.free_bytes.get() + SLOT_SIZE + len).into();

        #[cfg(debug_assertions)]
        self.compact();
    }

    pub(super) fn set_page_type(&mut self, page_type: BtreePageType) {
        self.page_type.set(page_type as u16);
        match page_type {
            BtreePageType::Leaf => {
                self.prefix.pgtype = PGTYPE_BTREELF;
            }
            BtreePageType::Inner => {
                self.prefix.pgtype = PGTYPE_BTREEIN;
            }
        }
    }

    /// Removes the entry with `key`. Does nothing if the key is not present.
    pub(super) fn delete(&mut self, key: &[u8]) {
        if let SearchResult::Found(slot_index) = self.find_slot_from_key(key) {
            self.delete_slot_entry(slot_index);
        }
    }

    /// MUST have the same length as the old value!!
    pub(super) fn overwrite_value_at_slot_index(&mut self, slot_index: u16, val: &[u8]) {
        mooo_assert!(self.len() > slot_index);
        let (_, value_slice) = self.key_val_slices_from_slot_mut(slot_index);
        mooo_assert!(value_slice.len() == val.len());
        value_slice.copy_from_slice(val);
    }

    fn insert_internal(&mut self, key: &[u8], val: &[u8], ordered: bool) -> bool {
        mooo_assert!(
            size_of::<SerializedU16>() + key.len() + val.len() <= MAX_ENTRY_LEN,
            "with a page size of {} the max btree entry length is {} (len={} passed)",
            PAGE_SIZE,
            MAX_ENTRY_LEN,
            key.len()
        );

        let entry_len = match self.has_space(key, val) {
            Err(()) => return false,
            Ok(entry_len) => entry_len,
        };

        if self.free_bytes_contig() < entry_len + SLOT_SIZE {
            self.compact();
        }

        let mut should_increment_slot_ptr = true;
        let slot_index = if ordered {
            match self.find_slot_from_key(key) {
                SearchResult::Found(slot_index) => {
                    should_increment_slot_ptr = false;
                    slot_index
                }
                SearchResult::NotFound(slot_index) => slot_index,
                SearchResult::Right => self.len(),
            }
        } else {
            self.len()
        };

        let offset = if should_increment_slot_ptr {
            match self.prepare_insert(slot_index, entry_len) {
                Some(off) => off as usize,
                None => return false,
            }
        } else {
            let off = self.lower_ptr.get() - entry_len + 1;
            self.write_slot(slot_index, off, entry_len);
            self.lower_ptr = (off - 1).into();
            self.free_bytes = (self.free_bytes.get() - entry_len).into();
            off as usize
        };

        // key-len
        SerializedU16::mut_from_prefix(&mut self.raw.as_mut()[offset..]).set(key.len() as u16);
        // key
        let key_start = offset + size_of::<SerializedU16>();
        self.raw.as_mut()[key_start..key_start + key.len()].copy_from_slice(key);
        // val
        let val_start = key_start + key.len();
        self.raw.as_mut()[val_start..val_start + val.len()].copy_from_slice(val);

        true
    }

    /// Inserts or updates `(key, val)` maintaining sorted order. Returns `false` if the page is full.
    pub(super) fn insert(&mut self, key: &[u8], val: &[u8]) -> bool {
        #[cfg(debug_assertions)]
        self.compact();

        self.insert_internal(key, val, true)
    }

    /// Appends `(key, val)` to the end of the slot array without a binary search.
    /// Note: Breaks the sort invariant unless the caller guarantees the entry belongs at the end.
    pub(super) fn insert_unordered(&mut self, key: &[u8], val: &[u8]) -> bool {
        #[cfg(debug_assertions)]
        self.compact();

        self.insert_internal(key, val, false)
    }

    pub(super) fn compact(&mut self) {
        let mut cloned_raw = [0u8; PAGE_SIZE];
        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = BtreePage::from_buffer(&mut cloned_raw);
        self.clear();
        for (k, v) in cloned_page.iter() {
            self.insert_internal(k, v, false);
        }
    }

    /// Moves the upper half of entries into `right_page`, which must be empty.
    /// Compacts both sides.
    pub(super) fn redistribute_into(&mut self, right_page: &mut Self) {
        mooo_assert!(right_page.is_initialized());
        mooo_assert!(right_page.len() == 0);

        let mut cloned_left_raw = [0u8; PAGE_SIZE];
        cloned_left_raw.copy_from_slice(self.raw());
        let og_page = BtreePage::from_buffer(&mut cloned_left_raw);
        self.clear();

        let midpoint = og_page.len() / 2;

        for (k, v) in (0..midpoint).map(|i| og_page.key_val_slices_from_slot(i)) {
            self.insert_unordered(k, v);
        }
        for (k, v) in (midpoint..og_page.len()).map(|i| og_page.key_val_slices_from_slot(i)) {
            right_page.insert_unordered(k, v);
        }

        #[cfg(debug_assertions)]
        {
            self.compact();
            right_page.compact();
        }
    }
}

// iterator

pub(super) struct SortedIterator<'a, Buf: AsRef<[u8]>> {
    page:       &'a BtreePage<Buf>,
    slot_index: u16,
}

impl<'a, Buf: AsRef<[u8]>> Iterator for SortedIterator<'a, Buf> {
    type Item = (&'a [u8], &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.slot_index == self.page.len() {
            return None;
        }
        let res = self.page.key_val_slices_from_slot(self.slot_index);
        self.slot_index += 1;
        Some(res)
    }
}

impl<'a, Buf: AsRef<[u8]>> IntoIterator for &'a BtreePage<Buf> {
    type Item = (&'a [u8], &'a [u8]);
    type IntoIter = SortedIterator<'a, Buf>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Outcome of a binary search over the slot array.
pub(super) enum SearchResult {
    /// The key was found at this slot index.
    Found(u16),
    /// The key was not found; this slot index is where it would be inserted.
    NotFound(u16),
    /// The key is greater than all entries; it belongs past the last slot.
    Right,
}
