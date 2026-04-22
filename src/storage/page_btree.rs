use std::ops::Deref;
use std::ops::DerefMut;

use super::PAGE_SIZE;
use super::page_base::END_OF_PAGE;
use super::page_base::PAGE_HEADER_SIZE;
use super::page_base::PagePrefix;
use super::page_base::SLOT_SIZE;
use super::serialization::Serialized;
use super::serialization::SerializedU16;
use super::serialization::SerializedU64;
use crate::mooo_assert;

// This line should give us a compile error if we set page-size too low
pub(crate) const BTREE_KEY_MAX_LEN: usize = ((PAGE_SIZE - PAGE_HEADER_SIZE as usize) / 2)
    - (SLOT_SIZE as usize)
    - size_of::<SerializedU64>();
const BTREE_PAGE_USABLE_SPACE: u16 = PAGE_SIZE as u16 - PAGE_HEADER_SIZE;

#[repr(C)]
pub(super) struct BtreePageHeader {
    pub(super) prefix:     PagePrefix,
    pub(super) page_type:  SerializedU16,
    pub(super) upper_ptr:  SerializedU16,
    pub(super) free_bytes: SerializedU16,
    pub(super) lower_ptr:  SerializedU16,
}
const _: () = mooo_assert!(size_of::<BtreePageHeader>() == PAGE_HEADER_SIZE as usize);
unsafe impl Serialized for BtreePageHeader {}

/// A sorted B-tree page storing key-value pairs in ascending key order.
pub(super) struct BtreePage<Buf> {
    raw: Buf,
}

// constructors

impl<'buf> BtreePage<&'buf mut [u8; PAGE_SIZE]> {
    pub(super) fn new_with_buffer(
        buffer: &'buf mut [u8; PAGE_SIZE], page_type: BtreePageType,
    ) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.clear_entries();
        page.set_page_type(page_type);
        page
    }

    pub(super) const fn from_buffer(buffer: &'buf mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }
}

impl<'b> BtreePage<&'b [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
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
        1 + self.lower_ptr.get() - self.upper_ptr.get()
    }

    fn free_bytes(&self) -> u16 {
        self.free_bytes.get()
    }

    pub(super) fn len(&self) -> u16 {
        (self.upper_ptr.get() - PAGE_HEADER_SIZE) / SLOT_SIZE
    }

    fn offset_len_from_slot(&self, slot_index: u16) -> (u16, u16) {
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_ref();
        (
            SerializedU16::ref_from_bytes(&raw[base..]).get(),
            SerializedU16::ref_from_bytes(&raw[base + size_of::<u16>()..]).get(),
        )
    }

    pub(super) fn is_leaf(&self) -> bool {
        self.page_type.get() == BtreePageType::Leaf as u16
    }

    pub(super) fn is_inner(&self) -> bool {
        self.page_type.get() == BtreePageType::Inner as u16
    }

    pub(super) fn get_page_type(&self) -> BtreePageType {
        if self.page_type.get() == BtreePageType::Inner as u16 {
            BtreePageType::Inner
        } else {
            BtreePageType::Leaf
        }
    }

    pub(super) fn is_half_full_or_more(&self) -> bool {
        (BTREE_PAGE_USABLE_SPACE - self.free_bytes_contig()) >= BTREE_PAGE_USABLE_SPACE / 2
    }

    /// Returns the `(key, value)` pair stored at `slot_index`.
    pub(super) fn entry_at_slot(&self, slot_index: u16) -> (&[u8], SerializedU64) {
        mooo_assert!(slot_index < self.len());

        let (offset, len) = self.offset_len_from_slot(slot_index);
        let val_size = size_of::<SerializedU64>() as u16;
        mooo_assert!(len >= val_size);
        let key_len = len - val_size;

        let raw = self.raw();
        (
            &raw[offset as usize..(offset + key_len) as usize],
            SerializedU64::read_from_bytes(
                &raw[(offset + key_len) as usize..(offset + key_len + val_size) as usize],
            ),
        )
    }

    /// Binary searches for `key` and returns a [`SearchResult`] indicating whether it was
    /// found and at which slot, or where it would be inserted to maintain order.
    fn find_slot_from_key(&self, key: &[u8]) -> SearchResult {
        let _ = u16::try_from(key.len()).expect("passed key too large");

        if self.len() == 0 {
            return SearchResult::Right;
        }

        let mut low = 0;
        let mut high = self.len();

        while low < high {
            let mid = low + (high - low) / 2;
            let (mid_key, _) = self.entry_at_slot(mid);

            match mid_key.cmp(key) {
                std::cmp::Ordering::Equal => return SearchResult::Found(mid),
                std::cmp::Ordering::Less => low = mid + 1,
                std::cmp::Ordering::Greater => high = mid,
            }
        }

        if low == self.len() { SearchResult::Right } else { SearchResult::NotFound(low) }
    }

    /// Returns an iterator over `(key, value)` pairs in ascending key order.
    pub(super) const fn iter(&self) -> SortedIterator<'_, Buf> {
        SortedIterator { page: self, slot_index: 0 }
    }

    /// Returns the value associated with `key`, or `None` if not present.
    pub(super) fn get(&self, key: &[u8]) -> Option<SerializedU64> {
        match self.find_slot_from_key(key) {
            SearchResult::Found(slot_index) => Some(self.entry_at_slot(slot_index).1),
            _ => None,
        }
    }

    /// Returns the child page to follow for `key` during tree traversal.
    ///
    /// Finds the last slot whose key does not exceed `key`. Slot 0 is a catch-all for any key
    /// smaller than slot 1's separator, so inner nodes never need their keys updated during descent.
    pub(super) fn get_traversal_next_page(&self, key: &[u8]) -> Option<(SerializedU64, u16)> {
        mooo_assert!(self.is_inner(), "shouldnt be called on leaf node");
        mooo_assert!(self.len() > 0, "inner node shouldnt be empty");

        let slot_index = match self.find_slot_from_key(key) {
            SearchResult::Found(slot_index) => slot_index,
            SearchResult::NotFound(slot_index) => slot_index.saturating_sub(1),
            SearchResult::Right => self.len() - 1,
        };
        Some((self.entry_at_slot(slot_index).1, slot_index))
    }

    fn has_space(&self, key: &[u8]) -> Result<u16, ()> {
        let entry_len =
            u16::try_from(key.len() + size_of::<SerializedU64>()).expect("entry too big for u16");
        if entry_len + SLOT_SIZE > self.free_bytes.get() {
            return Err(());
        }
        Ok(entry_len)
    }
}

// write impl

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> BtreePage<Buf> {
    fn write_slot(&mut self, slot_index: u16, offset: u16, len: u16) {
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_mut();
        SerializedU16::from(offset).write_to_prefix(&mut raw[base..]);
        SerializedU16::from(len).write_to_prefix(&mut raw[base + size_of::<u16>()..]);
    }

    fn clear_entries(&mut self) {
        self.upper_ptr = PAGE_HEADER_SIZE.into();
        self.lower_ptr = END_OF_PAGE.into();
        self.free_bytes = BTREE_PAGE_USABLE_SPACE.into();

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

    fn delete_slot_entry(&mut self, slot_index: u16) {
        assert!(slot_index < self.len());
        let (offset, len) = self.offset_len_from_slot(slot_index);

        let del = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let end = (PAGE_HEADER_SIZE + self.len() * SLOT_SIZE) as usize;
        self.raw.as_mut().copy_within(del + SLOT_SIZE as usize..end, del);

        self.upper_ptr = (self.upper_ptr.get() - SLOT_SIZE).into();
        self.free_bytes = (self.free_bytes.get() + SLOT_SIZE + len).into();

        #[cfg(debug_assertions)]
        {
            self.raw.as_mut()[offset as usize..(offset + len) as usize].fill(0);
            let stale = (PAGE_HEADER_SIZE + self.len() * SLOT_SIZE) as usize;
            self.raw.as_mut()[stale..stale + SLOT_SIZE as usize].fill(0);
        }
    }

    pub(super) fn set_page_type(&mut self, page_type: BtreePageType) {
        self.page_type.set(page_type as u16);
        self.prefix.dbg_pad = *match page_type {
            BtreePageType::Leaf => b"BtLf",
            BtreePageType::Inner => b"BtIn",
        };
    }

    /// Removes the entry with `key`. Does nothing if the key is not present.
    pub(super) fn delete(&mut self, key: &[u8]) {
        if let SearchResult::Found(slot_index) = self.find_slot_from_key(key) {
            self.delete_slot_entry(slot_index);
        }
    }

    pub(super) fn overwrite_value_with_slot_index(&mut self, slot_index: u16, val: SerializedU64) {
        let (offset, len) = self.offset_len_from_slot(slot_index);
        let start = offset as usize + len as usize - size_of::<SerializedU64>();
        self.raw.as_mut()[start..start + size_of::<SerializedU64>()]
            .copy_from_slice(val.as_bytes());
    }

    fn insert_internal(&mut self, key: &[u8], val: SerializedU64, ordered: bool) -> bool {
        mooo_assert!(
            key.len() <= BTREE_KEY_MAX_LEN,
            "with a page size of {} the max btree key length is {} (len={} passed)",
            PAGE_SIZE,
            BTREE_KEY_MAX_LEN,
            key.len()
        );

        let key_len = u16::try_from(key.len()).expect("key too large for u16");

        let entry_len = match self.has_space(key) {
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
                Some(off) => off,
                None => return false,
            }
        } else {
            let off = self.lower_ptr.get() - entry_len + 1;
            self.write_slot(slot_index, off, entry_len);
            self.lower_ptr = (off - 1).into();
            self.free_bytes = (self.free_bytes.get() - entry_len).into();
            off
        };

        self.raw.as_mut()[offset as usize..(offset + key_len) as usize].copy_from_slice(key);
        let val_size = size_of::<SerializedU64>() as u16;
        self.raw.as_mut()[(offset + key_len) as usize..(offset + key_len + val_size) as usize]
            .copy_from_slice(val.as_bytes());
        true
    }

    /// Inserts or updates `(key, val)` maintaining sorted order. Returns `false` if the page is full.
    pub(super) fn insert(&mut self, key: &[u8], val: SerializedU64) -> bool {
        self.insert_internal(key, val, true)
    }

    /// Appends `(key, val)` to the end of the slot array without a binary search.
    /// Note: Breaks the sort invariant unless the caller guarantees the entry belongs at the end.
    pub(super) fn insert_unordered(&mut self, key: &[u8], val: SerializedU64) -> bool {
        self.insert_internal(key, val, false)
    }

    fn compact(&mut self) {
        let mut cloned_raw = [0u8; PAGE_SIZE];
        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = BtreePage::from_buffer(&mut cloned_raw);
        self.clear_entries();
        for (k, v) in cloned_page.iter() {
            self.insert_unordered(k, v);
        }
    }

    /// Moves the upper half of entries into `right_page`, which must be empty.
    /// Compacts both sides.
    pub(super) fn redistribute_into(&mut self, right_page: &mut Self) {
        mooo_assert!(right_page.len() == 0);

        let mut cloned_left_raw = [0u8; PAGE_SIZE];
        cloned_left_raw.copy_from_slice(self.raw());
        let og_page = BtreePage::from_buffer(&mut cloned_left_raw);
        self.clear_entries();

        let midpoint = og_page.len() / 2;

        for (k, v) in (0..midpoint).map(|i| og_page.entry_at_slot(i)) {
            self.insert_unordered(k, v);
        }
        for (k, v) in (midpoint..og_page.len()).map(|i| og_page.entry_at_slot(i)) {
            right_page.insert_unordered(k, v);
        }
    }
}

// iterator

pub(super) struct SortedIterator<'a, Buf: AsRef<[u8]>> {
    page:       &'a BtreePage<Buf>,
    slot_index: u16,
}

impl<'a, Buf: AsRef<[u8]>> Iterator for SortedIterator<'a, Buf> {
    type Item = (&'a [u8], SerializedU64);

    fn next(&mut self) -> Option<Self::Item> {
        if self.slot_index == self.page.len() {
            return None;
        }
        let res = self.page.entry_at_slot(self.slot_index);
        self.slot_index += 1;
        Some(res)
    }
}

impl<'a, Buf: AsRef<[u8]>> IntoIterator for &'a BtreePage<Buf> {
    type Item = (&'a [u8], SerializedU64);
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
