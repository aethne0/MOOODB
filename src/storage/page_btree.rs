use std::ops::Deref;
use std::ops::DerefMut;

use super::page_base::BasePage;
use super::page_base::RangeExt;
use super::page_base::SLOT_SIZE;
use super::page_base::U64Entry;
use crate::storage::PAGE_SIZE;

/// A sorted B-tree page storing key-value pairs in ascending key order.
pub(super) struct BtreePage<Buf> {
    core: BasePage<Buf>,
}

// constructors

impl<'buf> BtreePage<&'buf mut [u8; PAGE_SIZE]> {
    pub(super) fn new_with_buffer(
        buffer: &'buf mut [u8; PAGE_SIZE], page_id: u64, parent: u64, right: u64,
    ) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.pad = *b"BTREE!!!";
        page.initialize_header(page_id, parent, right);
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

        if low == self.len() { SearchResult::Right } else { SearchResult::NotFound(low) }
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

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod test {
    use crate::storage::page_base::PAGE_HEADER_SIZE;
    use crate::storage::page_base::U64Entry;
    use crate::storage::page_btree::BtreePage;

    use super::PAGE_SIZE;
    use std::collections::BTreeMap;
    use std::collections::HashMap;
    use std::collections::HashSet;

    use rand::Rng;
    use rand::RngExt;
    use rand::SeedableRng;
    use rand::rngs::StdRng;
    use rand::seq::IteratorRandom;

    fn make_leaf_page(buffer: &mut [u8; PAGE_SIZE]) -> BtreePage<&mut [u8; PAGE_SIZE]> {
        BtreePage::new_with_buffer(buffer, 2, 1, 3)
    }

    #[test]
    fn test_page_insert_get() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut p = make_leaf_page(&mut buffer);

        let key = [1, 2, 3, 4];
        let val = U64Entry::from(0x123456789abcdef_u64);
        let res = p.insert(&key, val);

        assert!(res);

        let got = p.get(&key).unwrap();
        assert_eq!(got, val);
    }

    #[test]
    fn test_page_compaction_stable() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut key = [0u8; 6];

        for _ in 0..16 {
            rng.fill(&mut key);
            let val = U64Entry::from(rng.next_u64());
            if !the_page.insert(&key, val) {
                break;
            }
        }

        let mut buffer2 = [0u8; PAGE_SIZE];
        buffer2.copy_from_slice(the_page.raw());
        let mut the_other_page = BtreePage::from_buffer(&mut buffer2);
        the_other_page.compact();

        for ((k1, v1), (k2, v2)) in the_page.iter().zip(the_other_page.iter()) {
            assert_eq!(k1, k2);
            assert_eq!(v1, v2);
        }
    }

    #[test]
    fn test_page_compaction_frees() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut key = [0u8; 6];

        for _ in 0..16 {
            rng.fill(&mut key);
            let val = U64Entry::from(rng.next_u64());
            if !the_page.insert(&key, val) {
                break;
            }
        }

        let mut buffer2 = [0u8; PAGE_SIZE];
        buffer2.copy_from_slice(the_page.raw());
        let the_other_page = BtreePage::from_buffer(&mut buffer2);

        for (k, _) in the_other_page.iter() {
            the_page.delete(k);
        }

        the_page.compact();

        assert_eq!(the_page.free_bytes_contig(), (PAGE_SIZE - PAGE_HEADER_SIZE as usize) as u16);
    }

    #[test]
    fn test_compact_fragmented_increases_contiguous_free() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);
        let mut key = [0u8; 6];
        let mut val = U64Entry::from(0_u64);
        let mut keys = Vec::new();

        while page.insert(&key, val) {
            keys.push(key);
            rng.fill(&mut key);
            val = U64Entry::from(rng.next_u64());
        }
        let n = keys.len();
        assert!(n >= 4, "page should hold several entries");

        for k in keys.iter().skip(1).step_by(2) {
            page.delete(k);
        }
        let contig_before = page.free_bytes_contig();

        page.compact();

        let contig_after = page.free_bytes_contig();
        let total_free_after = page.free_bytes();
        assert!(contig_after >= contig_before, "compact should not reduce contiguous free");
        assert_eq!(
            contig_after, total_free_after,
            "after compact all free space should be contiguous"
        );
        assert_eq!(page.len() as usize, (n + 1) / 2);
    }

    #[test]
    fn test_insert_triggers_compact_when_fragmented() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(42);
        let mut key = [0u8; 6];
        let mut val = U64Entry::from(0_u64);
        let mut keys = Vec::new();

        while page.insert(&key, val) {
            keys.push(key);
            rng.fill(&mut key);
            val = U64Entry::from(rng.next_u64());
        }
        let n = keys.len();
        assert!(n >= 4);

        for k in keys.iter().take(n / 2) {
            page.delete(k);
        }
        let new_key = [0xffu8; 6];
        let new_val = U64Entry::from(0xeeeeeeeeeeeeeeee_u64);
        let inserted = page.insert(&new_key, new_val);
        assert!(inserted, "insert should compact and succeed when fragmented");
        assert!(page.get(&new_key).is_some_and(|v| v == new_val));
        assert_eq!(page.len() as usize, n - n / 2 + 1);
    }

    #[test]
    fn test_compact_then_insert_until_full() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);
        let mut key = [0u8; 6];
        let mut val = U64Entry::from(0_u64);
        let mut keys = Vec::new();

        while page.insert(&key, val) {
            keys.push(key);
            rng.fill(&mut key);
            val = U64Entry::from(rng.next_u64());
        }
        for k in keys.iter().skip(1).step_by(2) {
            page.delete(k);
        }
        page.compact();

        let mut prev_len = page.len() as usize;
        while page.insert(&key, val) {
            rng.fill(&mut key);
            val = U64Entry::from(rng.next_u64());
            prev_len += 1;
        }
        assert_eq!(page.len() as usize, prev_len);
        let mut prev: Option<&[u8]> = None;
        for (k, v) in page.iter() {
            assert_eq!(page.get(k), Some(v));
            if let Some(p) = prev {
                assert!(p < k);
            }
            prev = Some(k);
        }
    }

    #[test]
    fn test_page_churn() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut key = [0u8; 6];

        for _ in 0..PAGE_SIZE {
            rng.fill(&mut key);
            let val = U64Entry::from(rng.next_u64());
            let res = the_page.insert(&key, val);
            assert!(res, "Hmm... {}", the_page.len());
            the_page.delete(&key);
        }
    }

    #[test]
    fn test_page_delete() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut kvs = HashSet::new();

        let mut key = [0u8; 6];

        loop {
            rng.fill(&mut key);
            let val = U64Entry::from(rng.next_u64());

            let res = the_page.insert(&key, val);
            if !res {
                break;
            }

            kvs.insert(key.clone());
        }

        for k in &kvs {
            the_page.delete(k);
            let res = the_page.get(k);
            assert!(res.is_none());
        }

        assert_eq!(the_page.len(), 0);
    }

    #[test]
    fn test_page_insert_many() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut kvs = HashMap::new();

        let mut key = [0u8; 6];

        loop {
            rng.fill(&mut key);
            let val = U64Entry::from(rng.next_u64());

            let res = the_page.insert(&key, val);
            if !res {
                break;
            }

            kvs.insert(key.clone(), val);
        }

        let mut prev = None;
        for (k, v) in the_page.iter() {
            assert_eq!(v, *kvs.get(k).unwrap());
            if let Some(prev) = prev {
                assert!(prev < k);
            }
            prev = Some(k);
        }

        assert_eq!(the_page.iter().count(), kvs.len());
    }

    #[test]
    fn test_page_insert_many_unordered() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut kvs = vec![];

        let mut key = [0u8; 6];

        loop {
            rng.fill(&mut key);
            let val = U64Entry::from(rng.next_u64());

            let res = the_page.insert_unordered(&key, val);
            if !res {
                break;
            }

            kvs.push((key.clone(), val));
        }

        for ((k1, v1), (k2, v2)) in the_page.iter().zip(&kvs) {
            assert_eq!(k1, k2);
            assert_eq!(v1, *v2);
        }

        assert_eq!(the_page.iter().count(), kvs.len());
    }

    #[test]
    fn get_returns_none_on_empty_page() {
        let mut buffer = [0u8; PAGE_SIZE];
        let page = make_leaf_page(&mut buffer);

        assert!(page.get(&[1, 2, 3]).is_none());
    }

    #[test]
    fn get_returns_none_for_key_not_in_nonempty_page() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);
        page.insert(&[5], U64Entry::from(50_u64));

        assert!(page.get(&[1]).is_none()); // less than only entry
        assert!(page.get(&[9]).is_none()); // greater than only entry
        assert!(page.get(&[5, 0]).is_none()); // different key entirely
    }

    #[test]
    fn delete_missing_key_does_not_change_page() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);
        let key = [1u8, 2, 3];
        let val = U64Entry::from(42_u64);
        page.insert(&key, val);
        let len_before = page.len();
        let free_before = page.free_bytes();

        page.delete(&[9, 9, 9]);

        assert_eq!(page.len(), len_before);
        assert_eq!(page.free_bytes(), free_before);
        assert!(page.get(&key).is_some_and(|v| v == val));
    }

    #[test]
    fn iter_on_empty_page_yields_nothing() {
        let mut buffer = [0u8; PAGE_SIZE];
        let page = make_leaf_page(&mut buffer);

        assert_eq!(page.iter().count(), 0);
    }

    #[test]
    fn clear_empties_page() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);
        page.insert(&[1], U64Entry::from(1_u64));
        page.insert(&[2], U64Entry::from(2_u64));

        page.clear();

        assert_eq!(page.len(), 0);
        assert_eq!(page.iter().count(), 0);
        assert!(page.get(&[1]).is_none());
        assert!(page.get(&[2]).is_none());
    }

    #[test]
    fn compact_on_empty_page_is_safe() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        page.compact();

        assert_eq!(page.len(), 0);
        assert_eq!(page.free_bytes_contig(), (PAGE_SIZE - PAGE_HEADER_SIZE as usize) as u16);
    }

    #[test]
    fn insert_same_key_updates_value_and_preserves_count() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);
        let key = [1u8, 2, 3];
        let val1 = U64Entry::from(111_u64);
        let val2 = U64Entry::from(222_u64);

        assert!(page.insert(&key, val1));
        assert!(page.insert(&key, val2));

        assert_eq!(page.len(), 1);
        assert!(page.get(&key).is_some_and(|v| v == val2));
    }

    #[test]
    fn descending_insertion_order_iterates_ascending() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        for i in (0u8..8).rev() {
            assert!(page.insert(&[i], U64Entry::from(i as u64)));
        }

        let keys: Vec<u8> = page.iter().map(|(k, _)| k[0]).collect();
        let mut expected = keys.clone();
        expected.sort_unstable();
        assert_eq!(keys, expected);
        assert_eq!(page.len(), 8);
    }

    #[test]
    fn delete_first_and_last_elements_maintain_integrity() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);
        let entries = [
            ([1u8], U64Entry::from(10_u64)),
            ([5u8], U64Entry::from(50_u64)),
            ([9u8], U64Entry::from(90_u64)),
        ];
        for (k, v) in &entries {
            page.insert(&k[..], *v);
        }

        page.delete(&[1]);
        page.delete(&[9]);

        assert_eq!(page.len(), 1);
        assert!(page.get(&[1]).is_none());
        assert!(page.get(&[9]).is_none());
        assert!(page.get(&[5]).is_some_and(|v| v == U64Entry::from(50_u64)));
    }

    #[test]
    fn insert_returns_false_and_preserves_state_when_full() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);
        let mut rng = StdRng::seed_from_u64(99);
        let mut key = [0u8; 6];

        loop {
            if !page.insert(&key, U64Entry::from(0_u64)) {
                break;
            }
            rng.fill(&mut key);
        }

        let len_when_full = page.len();
        let free_when_full = page.free_bytes();

        // `key` is the one that just failed; try again
        let result = page.insert(&key, U64Entry::from(0xdead_u64));

        assert!(!result);
        assert_eq!(page.len(), len_when_full);
        assert_eq!(page.free_bytes(), free_when_full);
    }

    #[test]
    fn test_page_fuzzy() {
        let seed = 1;

        let mut buffer = [0u8; PAGE_SIZE];
        let mut pg = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(seed);

        let mut kvs: BTreeMap<Vec<u8>, U64Entry> = BTreeMap::new();

        const MAX_LEN: usize = 128;
        let mut key = Vec::with_capacity(MAX_LEN);

        for i in 0..10_000 {
            match rng.next_u32() % 1000 {
                0..3 => {
                    pg.clear();
                    kvs.clear();
                }
                3..400 => {
                    if kvs.is_empty() {
                        continue;
                    }

                    let (k, v) = kvs.iter().choose(&mut rng).unwrap();
                    let got_val = pg.get(k);
                    assert!(got_val.is_some_and(|x| x == *v), "failed @ i={i} (get)");
                }
                400..850 => {
                    let k: Vec<u8> = if (rng.next_u32() % 100) > 75 && !kvs.is_empty() {
                        kvs.iter().choose(&mut rng).unwrap().0.clone()
                    } else {
                        key.resize(rng.random_range(1..=MAX_LEN), 0);
                        rng.fill(key.as_mut_slice());
                        key.clone()
                    };

                    let val = U64Entry::from(rng.next_u64());

                    let res = pg.insert(&k, val);
                    if res {
                        kvs.insert(k, val);
                    }
                }
                850.. => {
                    if kvs.is_empty() {
                        continue;
                    }

                    let k = kvs.iter().choose(&mut rng).unwrap().0.clone();

                    pg.delete(&k);
                    let res = kvs.remove(&k);
                    assert!(res.is_some(), "failed @ i={i} (delete)");
                }
            }
        }

        let mut prev = None;
        for (k, v) in pg.iter() {
            assert_eq!(v, *kvs.get(k).unwrap());
            if let Some(prev) = prev {
                assert!(prev < k);
            }
            prev = Some(k);
        }

        for ((k1, v1), (k2, v2)) in pg.iter().zip(&kvs) {
            assert_eq!(k1, k2);
            assert_eq!(v1, *v2);
        }

        assert_eq!(pg.iter().count(), kvs.len());
    }

    #[test]
    fn test_update_free_accounting() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let key = b"mykey";
        let val1 = U64Entry::from(0x1111111111111111_u64);
        let val2 = U64Entry::from(0x2222222222222222_u64);

        assert!(page.insert(key, val1));
        let free_after_insert = page.free_bytes();

        assert!(page.insert(key, val2));
        let free_after_update = page.free_bytes();

        let entry_len = key.len() as u16 + U64Entry::SIZE_U16;
        assert_eq!(
            free_after_insert - free_after_update,
            entry_len,
            "update should consume entry_len bytes from free, not entry_len + SLOT_SIZE"
        );

        assert_eq!(page.get(key), Some(val2));
        assert_eq!(page.len(), 1);
    }

    #[test]
    fn test_readonly_view() {
        let mut buffer = [0u8; PAGE_SIZE];
        let val = U64Entry::from(0x123_u64);
        {
            let mut page = make_leaf_page(&mut buffer);
            page.insert(b"key", val);
        }
        let view = BtreePage::from_buffer_ref(&buffer);
        assert_eq!(view.get(b"key"), Some(val));
        assert_eq!(view.len(), 1);
    }
}
