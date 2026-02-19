use std::mem::size_of;
use std::ops::{Deref, DerefMut};

use crate::page::page_common::PageCommon;
use crate::page::{PageType, RangeExt, PAGE_SIZE, SLOT_SIZE};

pub(crate) struct PageSorted<'buffer> {
    core: PageCommon<'buffer>,
}

impl<'buffer> PageSorted<'buffer> {
    pub(crate) fn from_buffer(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self {
            core: PageCommon::from_buffer(buffer),
        }
    }

    pub(crate) fn new_with_buffer(
        buffer: &'buffer mut [u8; PAGE_SIZE],
        page_id: u64,
        page_type: PageType, // TODO
        parent: u64,
        right: u64,
    ) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.initialize_header(page_id, page_type, parent, right);
        page
    }

    pub(crate) fn clear(&mut self) {
        assert!(!self.is_free());
        self.clear_entries();
    }

    #[inline(always)]
    pub(crate) fn is_inner(&self) -> bool {
        self.page_type() == PageType::Inner as u8
    }

    #[inline(always)]
    pub(crate) fn is_leaf(&self) -> bool {
        self.page_type() == PageType::Leaf as u8
    }


    fn key_at_slot(&self, slot_index: u16) -> &[u8] {
        assert!(!self.is_free());
        assert!(slot_index < self.len());

        let offset = self.offset_from_slot(slot_index);
        let length = self.read_u16(offset);
        let start = offset + SLOT_SIZE;

        &self.raw()[(start..start + length).as_usizes()]
    }

    fn key_val_at_slot(&self, slot_index: u16) -> (&[u8], &[u8]) {
        assert!(!self.is_free());
        assert!(slot_index < self.len());

        let offset = self.offset_from_slot(slot_index);
        let key_len = self.read_u16(offset);
        let key_start = offset + SLOT_SIZE;
        let val_len = self.read_u16(key_start + key_len);
        let val_start = key_start + key_len + SLOT_SIZE;

        let raw = self.raw();
        (
            &raw[(key_start..key_start + key_len).as_usizes()],
            &raw[(val_start..val_start + val_len).as_usizes()],
        )
    }

    /// Returns slot-index of first element not-less-than the search key (left-most that is GE)
    fn find_key_slot(&self, key: &[u8]) -> SearchResult {
        assert!(self.is_inner() || self.is_leaf());
        let _ = u16::try_from(key.len()).expect("passed key too large");

        if self.len() == 0 {
            return SearchResult::Right;
        }

        let mut low = 0;
        let mut high = self.len();

        while low < high {
            let mid = low + (high - low) / 2;
            let mid_key = self.key_at_slot(mid);

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

    pub(crate) fn compact(&mut self) {
        assert!(!self.is_free());

        let mut cloned_raw = [0u8; PAGE_SIZE];
        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = PageSorted::from_buffer(&mut cloned_raw);

        self.clear_entries();

        for (k, v) in cloned_page.iter() {
            self.insert_unordered(k, v);
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> PageSortedIterator<'a> {
        assert!(!self.is_free());
        PageSortedIterator {
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
            let (k, v) = self.key_val_at_slot(slot_index);
            let entry_len = (k.len() + v.len() + 2 * size_of::<u16>()) as u16;
            self.delete_slot_at(slot_index, entry_len);
        }
    }

    fn has_space(&self, key: &[u8], val: &[u8]) -> Result<u16, ()> {
        let entry_len = u16::try_from(size_of::<u16>() * 2 + val.len() + key.len())
            .expect("entry too big for u16");

        if !self.has_space_entry(entry_len) {
            return Err(());
        }
        Ok(entry_len)
    }

    fn insert_internal(&mut self, key: &[u8], val: &[u8], ordered: bool) -> bool {
        assert!(!self.is_free());
        let key_len = u16::try_from(key.len()).expect("key too large for u16");
        let val_len = u16::try_from(val.len()).expect("val too large for u16");

        let entry_len = match self.has_space(key, val) {
            Err(()) => return false,
            Ok(entry_len) => entry_len,
        };

        if self.free_bytes_contig() < (entry_len + SLOT_SIZE)
            && self.free() >= (entry_len + SLOT_SIZE)
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
            let lower = self.lower_ptr();
            let free = self.free();
            let off = lower - entry_len + 1;
            self.write_slot(slot_index, off);
            self.set_lower_ptr(lower - entry_len);
            self.set_free(free - entry_len - SLOT_SIZE);
            off
        };

        self.raw_mut()[(offset..offset + SLOT_SIZE).as_usizes()]
            .copy_from_slice(&(key.len() as u16).to_be_bytes());

        let mut off = offset + SLOT_SIZE;
        self.raw_mut()[(off..off + key_len).as_usizes()].copy_from_slice(key);
        off += key_len;
        self.raw_mut()[(off..off + SLOT_SIZE).as_usizes()].copy_from_slice(&val_len.to_be_bytes());
        off += SLOT_SIZE;
        self.raw_mut()[(off..off + val_len).as_usizes()].copy_from_slice(val);

        true
    }

    #[inline(always)]
    pub(crate) fn insert(&mut self, key: &[u8], val: &[u8]) -> bool {
        self.insert_internal(key, val, true)
    }

    /// Inserts entry to the end of the slot array. This WILL break ordering invarients.
    /// Sorted page has this method because when we recompact we just reinsert all the entries from
    /// the original version of the page into the new copy of the page, and they are already
    /// sorted because we are iterating over them in order. We don't need the overhead of the
    /// binary search for each insert in this case.
    #[inline(always)]
    fn insert_unordered(&mut self, key: &[u8], val: &[u8]) -> bool {
        self.insert_internal(key, val, false)
    }
}

impl<'buffer> Deref for PageSorted<'buffer> {
    type Target = PageCommon<'buffer>;

    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

impl<'buffer> DerefMut for PageSorted<'buffer> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.core
    }
}

pub(crate) struct PageSortedIterator<'a> {
    page: &'a PageSorted<'a>,
    slot_index: u16,
}

impl<'a> Iterator for PageSortedIterator<'a> {
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

impl<'a> IntoIterator for &'a PageSorted<'a> {
    type Item = (&'a [u8], &'a [u8]);
    type IntoIter = PageSortedIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub(crate) enum SearchResult {
    Found(u16),
    NotFound(u16),
    Right,
}

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, HashMap, HashSet};

    use claims::{assert_lt, assert_none, assert_some, assert_some_eq};
    use rand::{rngs::StdRng, seq::IteratorRandom, Rng, RngExt, SeedableRng};

    use crate::page::{page_sorted::PageSorted, PageType, PAGE_HEADER_SIZE, PAGE_SIZE};

    fn make_leaf_page(buffer: &mut [u8; PAGE_SIZE]) -> PageSorted<'_> {
        PageSorted::new_with_buffer(buffer, 2, PageType::Leaf, 1, 3)
    }

    #[test]
    fn test_page_insert_get() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut p = make_leaf_page(&mut buffer);

        let key = [1, 2, 3, 4];
        let val = [5, 6, 7, 8];
        let res = p.insert(&key, &val);

        assert!(res);

        let got = p.get(&key);

        assert_eq!(got, Some(&val[..]));
    }

    #[test]
    fn test_page_compaction_stable() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut key = [0u8; 6];
        let mut val = [0u8; 6];

        for _ in 0..16 {
            rng.fill(&mut key);
            rng.fill(&mut val);
            if !the_page.insert(&key, &val) {
                break;
            }
        }

        let mut buffer2 = [0u8; PAGE_SIZE];
        buffer2.copy_from_slice(the_page.raw());
        let mut the_other_page = PageSorted::from_buffer(&mut buffer2);
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
        let mut val = [0u8; 6];

        for _ in 0..16 {
            rng.fill(&mut key);
            rng.fill(&mut val);
            if !the_page.insert(&key, &val) {
                break;
            }
        }

        let mut buffer2 = [0u8; PAGE_SIZE];
        buffer2.copy_from_slice(the_page.raw());
        let the_other_page = PageSorted::from_buffer(&mut buffer2);

        for (k, _) in the_other_page.iter() {
            the_page.delete(k);
        }

        the_page.compact();

        assert_eq!(
            the_page.free_bytes_contig(),
            (PAGE_SIZE - PAGE_HEADER_SIZE as usize) as u16
        );
    }

    /// Fragment the page (insert many, delete some), then compact. Contiguous free should
    /// increase and equal total free (all free space is one block after compact).
    #[test]
    fn test_compact_fragmented_increases_contiguous_free() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);
        let mut key = [0u8; 6];
        let mut val = [0u8; 6];
        let mut keys = Vec::new();

        while page.insert(&key, &val) {
            keys.push(key);
            rng.fill(&mut key);
            rng.fill(&mut val);
        }
        let n = keys.len();
        assert!(n >= 4, "page should hold several entries");

        // Delete every other entry to fragment the page
        for k in keys.iter().skip(1).step_by(2) {
            page.delete(k);
        }
        let contig_before = page.free_bytes_contig();

        page.compact();

        let contig_after = page.free_bytes_contig();
        let total_free_after = page.free();
        assert!(
            contig_after >= contig_before,
            "compact should not reduce contiguous free"
        );
        assert_eq!(
            contig_after, total_free_after,
            "after compact all free space should be contiguous"
        );
        assert_eq!(page.len() as usize, (n + 1) / 2);
    }

    /// When the page is fragmented (enough total free but not enough contiguous), insert
    /// should trigger compact and then succeed.
    #[test]
    fn test_insert_triggers_compact_when_fragmented() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(42);
        let mut key = [0u8; 6];
        let mut val = [0u8; 6];
        let mut keys = Vec::new();

        while page.insert(&key, &val) {
            keys.push(key);
            rng.fill(&mut key);
            rng.fill(&mut val);
        }
        let n = keys.len();
        assert!(n >= 4);

        // Delete a bunch of entries to fragment (holes in body)
        for k in keys.iter().take(n / 2) {
            page.delete(k);
        }
        let new_key = [0xffu8; 6];
        let new_val = [0xeeu8; 6];
        let inserted = page.insert(&new_key, &new_val);
        assert!(
            inserted,
            "insert should compact and succeed when fragmented"
        );
        assert_some_eq!(page.get(&new_key), &new_val[..]);
        assert_eq!(page.len() as usize, n - n / 2 + 1);
    }

    /// After compacting a fragmented page, we can insert until full again.
    #[test]
    fn test_compact_then_insert_until_full() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);
        let mut key = [0u8; 6];
        let mut val = [0u8; 6];
        let mut keys = Vec::new();

        while page.insert(&key, &val) {
            keys.push(key);
            rng.fill(&mut key);
            rng.fill(&mut val);
        }
        for k in keys.iter().skip(1).step_by(2) {
            page.delete(k);
        }
        page.compact();

        let mut prev_len = page.len() as usize;
        while page.insert(&key, &val) {
            rng.fill(&mut key);
            rng.fill(&mut val);
            prev_len += 1;
        }
        assert_eq!(page.len() as usize, prev_len);
        let mut prev: Option<&[u8]> = None;
        for (k, v) in page.iter() {
            assert_eq!(page.get(k), Some(v));
            if let Some(p) = prev {
                assert_lt!(p, k);
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
        let mut val = [0u8; 6];

        for _ in 0..PAGE_SIZE {
            rng.fill(&mut key);
            rng.fill(&mut val);
            let res = the_page.insert(&key, &val);
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
        let mut val = [0u8; 6];

        loop {
            rng.fill(&mut key);
            rng.fill(&mut val);

            let res = the_page.insert(&key, &val);
            if !res {
                break;
            }

            kvs.insert(key.clone());
        }

        for k in &kvs {
            the_page.delete(k);
            let res = the_page.get(k);
            assert_none!(res);
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
        let mut val = [0u8; 6];

        loop {
            rng.fill(&mut key);
            rng.fill(&mut val);

            let res = the_page.insert(&key, &val);
            if !res {
                break;
            }

            kvs.insert(key.clone(), val.clone());
        }

        let mut prev = None;
        for (k, v) in the_page.iter() {
            assert_eq!(v, kvs.get(k).unwrap());
            if let Some(prev) = prev {
                assert_lt!(prev, k);
            }
            prev = Some(k);
        }

        assert_eq!(the_page.iter().count(), kvs.len());
    }

    /// Tests insert_unordered (append-only, no binary search) on a PageSorted.
    /// Uses Leaf type; we only care that insertion order is preserved in iter().
    #[test]
    fn test_page_insert_many_unordered() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(0);

        let mut kvs = vec![];

        let mut key = [0u8; 6];
        let mut val = [0u8; 6];

        loop {
            rng.fill(&mut key);
            rng.fill(&mut val);

            let res = the_page.insert_unordered(&key, &val);
            if !res {
                break;
            }

            kvs.push((key.clone(), val.clone()));
        }

        for ((k1, v1), (k2, v2)) in the_page.iter().zip(&kvs) {
            assert_eq!(k1, k2);
            assert_eq!(v1, v2);
        }

        assert_eq!(the_page.iter().count(), kvs.len());
    }

    #[test]
    fn test_page_fuzzy() {
        let seed = 1;

        let mut buffer = [0u8; PAGE_SIZE];
        let mut pg = make_leaf_page(&mut buffer);

        let mut rng = StdRng::seed_from_u64(seed);

        let mut kvs: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();

        const MAX_LEN: usize = 128;
        let mut key = Vec::with_capacity(MAX_LEN);
        let mut val = Vec::with_capacity(MAX_LEN);

        for i in 0..1_000_000 {
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
                    assert_some_eq!(got_val, v, "failed @ i={i} (get)");
                }
                400..850 => {
                    let k = if (rng.next_u32() % 100) > 75 && pg.len() > 0 {
                        kvs.iter().choose(&mut rng).unwrap().0
                    } else {
                        key.resize(rng.random_range(1..=MAX_LEN), 0);
                        rng.fill(&mut key);
                        &key
                    };

                    val.resize(rng.random_range(1..=MAX_LEN), 0);
                    rng.fill(&mut val);

                    let res = pg.insert(k, &val);
                    if res {
                        kvs.insert(k.clone(), val.clone());
                    }
                }
                850.. => {
                    if kvs.is_empty() {
                        continue;
                    }

                    let k = kvs.iter().choose(&mut rng).unwrap().0.clone();

                    pg.delete(&k);
                    let res = kvs.remove(&k);
                    assert_some!(res, "failed @ i={i} (delete)");
                }
            }
        }

        let mut prev = None;
        for (k, v) in pg.iter() {
            assert_eq!(v, kvs.get(k).unwrap());
            if let Some(prev) = prev {
                assert_lt!(prev, k);
            }
            prev = Some(k);
        }

        for ((k1, v1), (k2, v2)) in pg.iter().zip(&kvs) {
            assert_eq!(k1, k2);
            assert_eq!(v1, v2);
        }

        assert_eq!(pg.iter().count(), kvs.len());
    }
}
