use std::ops::{Deref, DerefMut};

use crate::page::{page_common::PageCommon, PageType, RangeExt, PAGE_SIZE, SLOT_SIZE};

pub(crate) struct PageHeap<'buffer> {
    core: PageCommon<'buffer>,
}

impl<'buffer> PageHeap<'buffer> {
    pub(crate) fn from_buffer(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self {
            core: PageCommon::from_buffer(buffer),
        }
    }

    pub(crate) fn new_with_buffer(
        buffer: &'buffer mut [u8; PAGE_SIZE],
        page_id: u64,
        parent: u64,
        right: u64,
    ) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.initialize_header(page_id, PageType::Heap, parent, right);
        page
    }

    pub(crate) fn clear(&mut self) {
        assert!(self.is_heap());
        self.clear_entries();
    }

    fn val_at_slot(&self, slot_index: u16) -> &[u8] {
        assert!(self.is_heap());
        assert!(slot_index < self.len());

        let offset = self.offset_from_slot(slot_index);
        let start = offset + SLOT_SIZE;
        let end = start + self.read_u16(offset);

        &self.raw()[(start..end).as_usizes()]
    }

    pub(crate) fn compact(&mut self) {
        assert!(self.is_heap());

        let mut cloned_raw = [0u8; PAGE_SIZE];
        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = PageHeap::from_buffer(&mut cloned_raw);

        self.clear_entries();

        for (_, v) in cloned_page.iter() {
            self.append(v);
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> PageHeapIterator<'a> {
        assert!(self.is_heap());
        PageHeapIterator {
            page: self,
            slot_index: 0,
        }
    }

    pub(crate) fn get_at_slot(&self, slot_index: u16) -> Option<&[u8]> {
        assert!(self.is_heap());

        if slot_index >= self.len() {
            return None;
        }
        Some(self.val_at_slot(slot_index))
    }

    pub(crate) fn delete_at_slot(&mut self, slot_index: u16) {
        assert!(self.is_heap());

        if slot_index >= self.len() {
            return;
        }

        let offset = self.offset_from_slot(slot_index);
        let val_len = self.read_u16(offset);
        let entry_len = SLOT_SIZE + val_len;
        self.delete_slot_at(slot_index, entry_len);
    }

    pub(crate) fn append(&mut self, val: &[u8]) -> Option<u16> {
        assert!(self.is_heap());
        let entry_len = u16::try_from(usize::from(SLOT_SIZE) + val.len()).unwrap();

        if !self.has_space_entry(entry_len) {
            return None;
        }

        if self.free_bytes_contig() < (entry_len + SLOT_SIZE)
            && self.free() >= (entry_len + SLOT_SIZE)
        {
            self.compact();
        }

        let slot_index = self.len();
        let offset = match self.prepare_insert(slot_index, entry_len) {
            Some(off) => off,
            None => return None,
        };

        self.write_u16(offset, val.len() as u16);
        self.raw_mut()[(offset + SLOT_SIZE..offset + entry_len).as_usizes()].copy_from_slice(val);

        Some(slot_index)
    }
}

impl<'buffer> Deref for PageHeap<'buffer> {
    type Target = PageCommon<'buffer>;

    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

impl<'buffer> DerefMut for PageHeap<'buffer> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.core
    }
}

pub(crate) struct PageHeapIterator<'a> {
    page: &'a PageHeap<'a>,
    slot_index: u16,
}

impl<'a> Iterator for PageHeapIterator<'a> {
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

impl<'a> IntoIterator for &'a PageHeap<'a> {
    type Item = (u16, &'a [u8]);
    type IntoIter = PageHeapIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀

#[cfg(test)]
mod tests {
    use crate::page::PAGE_HEADER_SIZE;

    use super::*;

    #[test]
    fn test_heap_append_get() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageHeap::new_with_buffer(&mut buffer, 1, 0, 0);

        let data1 = b"hello";
        let data2 = b"world";

        let s1 = page.append(data1).unwrap();
        let s2 = page.append(data2).unwrap();

        assert_eq!(page.get_at_slot(s1), Some(&data1[..]));
        assert_eq!(page.get_at_slot(s2), Some(&data2[..]));
        assert_eq!(page.len(), 2);
    }

    #[test]
    fn test_heap_delete() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageHeap::new_with_buffer(&mut buffer, 1, 0, 0);

        page.append(b"item1").unwrap();
        page.append(b"item2").unwrap();

        page.delete_at_slot(0);
        assert_eq!(page.len(), 1);
        assert_eq!(page.get_at_slot(0), Some(&b"item2"[..]));
    }

    #[test]
    fn test_heap_iter() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageHeap::new_with_buffer(&mut buffer, 1, 0, 0);

        page.append(b"a").unwrap();
        page.append(b"b").unwrap();
        page.append(b"c").unwrap();

        let mut it = page.iter();
        assert_eq!(it.next(), Some((0, &b"a"[..])));
        assert_eq!(it.next(), Some((1, &b"b"[..])));
        assert_eq!(it.next(), Some((2, &b"c"[..])));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_heap_compaction() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageHeap::new_with_buffer(&mut buffer, 1, 0, 0);

        for i in 0..10 {
            if page.append(&[i as u8; 100]).is_none() {
                break;
            }
        }

        let free_before = page.free();

        for i in (0..page.len()).step_by(2).rev() {
            page.delete_at_slot(i as u16);
        }

        assert!(page.free() > free_before);
        assert!(page.free() > page.free_bytes_contig());

        page.compact();

        assert_eq!(page.free(), page.free_bytes_contig());

        for (i, (_, val)) in page.iter().enumerate() {
            let expected_val = (i * 2 + 1) as u8;
            assert_eq!(val, &[expected_val; 100]);
        }
    }

    #[test]
    fn test_heap_clear() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = PageHeap::new_with_buffer(&mut buffer, 1, 0, 0);

        page.append(b"data").unwrap();
        assert_eq!(page.len(), 1);

        page.clear();
        assert_eq!(page.len(), 0);
        assert_eq!(page.free(), PAGE_SIZE as u16 - PAGE_HEADER_SIZE);
    }
}
