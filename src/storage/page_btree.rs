use std::ops::Deref;
use std::ops::DerefMut;

use super::page_base::BasePage;
use super::page_base::RangeExt;
use super::page_base::U64Entry;
use super::page_base::SLOT_SIZE;
use crate::storage::PAGE_SIZE;

/// A sorted B-tree page storing key-value pairs in ascending key order.
pub(super) struct BtreePage<Buf> {
    core: BasePage<Buf>,
}

// constructors

impl<'buf> BtreePage<&'buf mut [u8; PAGE_SIZE]> {
    pub(super) fn new_with_buffer(
        buffer: &'buf mut [u8; PAGE_SIZE], parent: u64, right: u64,
    ) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.prefix.pad = *b"BTREE!!!";
        page.initialize_header(parent, right);
        page
    }

    pub(super) const fn from_buffer(buffer: &'buf mut [u8; PAGE_SIZE]) -> Self {
        Self { core: BasePage::from_buffer(buffer) }
    }
}

impl<'b> BtreePage<&'b [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        Self { core: BasePage::from_buffer_ref(buffer) }
    }
}

// read impl
const TYPE_LEAF: u16 = 0;
const TYPE_INNER: u16 = 1;

impl<Buf: AsRef<[u8]>> BtreePage<Buf> {
    pub(super) fn is_leaf(&self) -> bool {
        // TODO - use generic page flags field
        self.page_flags.get() == TYPE_LEAF
    }

    /// Returns the `(key, value)` pair stored at `slot_index`.
    fn entry_at_slot(&self, slot_index: u16) -> (&[u8], U64Entry) {
        assert!(slot_index < self.len());

        let (offset, len) = self.offset_len_from_slot(slot_index);
        assert!(len >= U64Entry::SIZE_U16);
        let key_len = len - U64Entry::SIZE_U16;

        let raw = self.raw();
        (
            &raw[(offset..offset + key_len).into_usizes()],
            U64Entry::from(
                &raw[(offset + key_len..offset + key_len + U64Entry::SIZE_U16).into_usizes()],
            ),
        )
    }

    /// Binary searches for `key` and returns a [`SearchResult`] indicating whether it was
    /// found and at which slot, or where it would be inserted to maintain order.
    fn find_key_slot(&self, key: &[u8]) -> SearchResult {
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
    pub(super) fn get(&self, key: &[u8]) -> Option<U64Entry> {
        match self.find_key_slot(key) {
            SearchResult::Found(slot_index) => Some(self.entry_at_slot(slot_index).1),
            _ => None,
        }
    }

    /// TODO rename
    /// gets first slot that is AT LEAST key (slot_key >= arg_key)
    /// This corresponds to which child page you should go it in a tree traversal
    pub(super) fn get_first_slot_ge_key(&self, key: &[u8]) -> Option<U64Entry> {
        assert!(!self.is_leaf(), "shouldnt be called on leaf node");
        assert!(self.len() > 0, "inner node shouldnt be empty");

        match self.find_key_slot(key) {
            SearchResult::Found(slot_index) | SearchResult::NotFound(slot_index) => {
                Some(self.entry_at_slot(slot_index).1)
            }
            _ => None,
        }
    }

    fn has_space(&self, key: &[u8]) -> Result<u16, ()> {
        let entry_len =
            u16::try_from(key.len() + size_of::<U64Entry>()).expect("entry too big for u16");
        if !self.has_space_entry(entry_len) {
            return Err(());
        }
        Ok(entry_len)
    }
}

// write impl

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> BtreePage<Buf> {
    pub(super) fn set_is_leaf(&mut self, is_leaf: bool) {
        self.page_flags.set(if is_leaf { TYPE_LEAF } else { TYPE_INNER });
    }

    /// Removes all entries, reclaiming all entry space.
    pub(super) fn clear(&mut self) {
        self.clear_entries();
    }

    /// Removes the entry with `key`. Does nothing if the key is not present.
    pub(super) fn delete(&mut self, key: &[u8]) {
        if let SearchResult::Found(slot_index) = self.find_key_slot(key) {
            self.delete_slot_entry(slot_index);
        }
    }

    /// Core insert path. When `ordered` is `true`, uses binary search to find the correct
    /// position and handles in-place update if the key already exists. When `false`,
    /// appends to the end of the slot array without a search (caller must ensure order).
    fn insert_internal(&mut self, key: &[u8], pk: U64Entry, ordered: bool) -> bool {
        // TODO refactor this and heap_page::append() to nto duplicate code
        let key_len = u16::try_from(key.len()).expect("key too large for u16");

        let entry_len = match self.has_space(key) {
            Err(()) => return false,
            Ok(entry_len) => entry_len,
        };

        if self.free_bytes_contig() < (entry_len + SLOT_SIZE)
            && self.free_bytes() >= (entry_len + SLOT_SIZE)
        {
            self.compact();
        }

        let mut should_increment_slot_ptr = true;
        let slot_index = if ordered {
            match self.find_key_slot(key) {
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
            if !self.has_space_entry(entry_len) {
                return false;
            }
            let lower = self.lower_ptr.get();
            let free = self.free_bytes.get();
            let off = lower - entry_len + 1;
            self.write_slot(slot_index, off, entry_len);
            self.lower_ptr = (lower - entry_len).into();
            self.free_bytes = (free - entry_len).into();
            off
        };

        self.raw_mut()[(offset..offset + key_len).into_usizes()].copy_from_slice(key);
        self.raw_mut()[(offset + key_len..offset + key_len + U64Entry::SIZE_U16).into_usizes()]
            .copy_from_slice(pk.as_bytes());
        true
    }

    /// Inserts or updates `(key, val)` maintaining sorted order. Returns `false` if the page is full.
    pub(super) fn insert(&mut self, key: &[u8], pk: U64Entry) -> bool {
        self.insert_internal(key, pk, true)
    }

    /// Appends `(key, val)` to the end of the slot array without a binary search.
    /// **Breaks the sort invariant** unless the caller guarantees the entry belongs at the end.
    pub(super) fn insert_unordered(&mut self, key: &[u8], pk: U64Entry) -> bool {
        self.insert_internal(key, pk, false)
    }

    /// Defragments the page by rewriting all live entries into a contiguous block. Sort order is preserved.
    pub(super) fn compact(&mut self) {
        let mut cloned_raw = [0u8; PAGE_SIZE];

        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = BtreePage::from_buffer(&mut cloned_raw);

        self.clear_entries();

        for (k, v) in cloned_page.iter() {
            self.insert_unordered(k, v);
        }
    }
}

// deref

impl<Buf: AsRef<[u8]>> Deref for BtreePage<Buf> {
    type Target = BasePage<Buf>;

    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> DerefMut for BtreePage<Buf> {
    fn deref_mut(&mut self) -> &mut BasePage<Buf> {
        &mut self.core
    }
}

// iterator

pub(super) struct SortedIterator<'a, Buf: AsRef<[u8]>> {
    page:       &'a BtreePage<Buf>,
    slot_index: u16,
}

impl<'a, Buf: AsRef<[u8]>> Iterator for SortedIterator<'a, Buf> {
    type Item = (&'a [u8], U64Entry);

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
    type Item = (&'a [u8], U64Entry);
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

