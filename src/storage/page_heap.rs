use std::ops::Deref;
use std::ops::DerefMut;

use super::page_base::*;
use super::PAGE_SIZE;

pub(super) struct HeapPage<Buf> {
    core: BasePage<Buf>,
}

// constructors

impl<'b> HeapPage<&'b mut [u8; PAGE_SIZE]> {
    /// Wraps `buffer` as a `PageHeap`. Does not initialize or validate any fields.
    pub(super) const fn from_buffer(buffer: &'b mut [u8; PAGE_SIZE]) -> Self {
        Self { core: BasePage::from_buffer(buffer) }
    }

    /// Wraps `buffer` as a `PageHeap` and initializes the page header.
    pub(super) fn new_with_buffer(buffer: &'b mut [u8; PAGE_SIZE]) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.clear_entries();
        page.prefix.dbg_pad = *b"HEAP";
        page
    }
}

impl<'b> HeapPage<&'b [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        Self { core: BasePage::from_buffer_ref(buffer) }
    }
}

// write impl
impl<B: AsRef<[u8]> + AsMut<[u8]>> HeapPage<B> {
    /// Appends `val` to the page and returns its slot index.
    ///
    /// Triggers compaction automatically if there is enough total free space but
    /// not enough contiguous space. Returns `None` if the page was full.
    /// If the page was full no changes were made**
    pub(super) fn append(&mut self, val: &[u8]) -> Option<u16> {
        // TODO refactor this and btree_page::() to nto duplicate code
        let entry_len = u16::try_from(val.len()).expect("val too long");

        if !self.has_space_entry(entry_len) {
            return None;
        }

        if self.free_bytes_contig() < (entry_len + SLOT_SIZE)
            && self.free_bytes() >= (entry_len + SLOT_SIZE)
        {
            self.compact();
        }

        let slot_index = self.len();
        let offset = self.prepare_insert(slot_index, entry_len)?;
        self.raw_mut()[(offset..offset + entry_len).into_usizes()].copy_from_slice(val);

        Some(slot_index)
    }

    /// Defragments the page by rewriting all live entries into a contiguous block,
    /// making all free space available as a single region.
    pub(super) fn compact(&mut self) {
        // hopefully compiler elides this zero-ing

        // TODO figure something else out for this memory eventually
        // TODO this should just copy into the other buffer, cause were copy on write
        // infact we can make it so its never called, if we copy by iterating
        let mut cloned_raw = [0u8; PAGE_SIZE];

        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = HeapPage::from_buffer(&mut cloned_raw);

        self.clear_entries();

        for (_, v) in cloned_page.iter() {
            self.append(v);
        }
    }
}

// deref

impl<B: AsRef<[u8]>> Deref for HeapPage<B> {
    type Target = BasePage<B>;

    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

impl<B: AsRef<[u8]> + AsMut<[u8]>> DerefMut for HeapPage<B> {
    fn deref_mut(&mut self) -> &mut BasePage<B> {
        &mut self.core
    }
}

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_heap_append_get() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = HeapPage::new_with_buffer(&mut buffer);

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
        let mut page = HeapPage::new_with_buffer(&mut buffer);

        page.append(b"item1").unwrap();
        page.append(b"item2").unwrap();

        page.delete_slot_entry(0);
        assert_eq!(page.len(), 1);
        assert_eq!(page.get_at_slot(0), Some(&b"item2"[..]));
    }

    #[test]
    fn test_heap_iter() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = HeapPage::new_with_buffer(&mut buffer);

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
        let mut page = HeapPage::new_with_buffer(&mut buffer);

        for i in 0..10 {
            if page.append(&[i as u8; 100]).is_none() {
                break;
            }
        }

        let free_before = page.free_bytes();

        for i in (0..page.len()).step_by(2).rev() {
            page.delete_slot_entry(i as u16);
        }

        assert!(page.free_bytes() > free_before);
        assert!(page.free_bytes() > page.free_bytes_contig());

        page.compact();

        assert_eq!(page.free_bytes(), page.free_bytes_contig());

        for (i, (_, val)) in page.iter().enumerate() {
            let expected_val = (i * 2 + 1) as u8;
            assert_eq!(val, &[expected_val; 100]);
        }
    }

    #[test]
    fn test_heap_clear() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut page = HeapPage::new_with_buffer(&mut buffer);

        page.append(b"data").unwrap();
        assert_eq!(page.len(), 1);

        page.clear_entries();
        assert_eq!(page.len(), 0);
        assert_eq!(page.free_bytes(), PAGE_SIZE as u16 - PAGE_HEADER_SIZE);
    }

    #[test]
    fn test_readonly_view() {
        let mut buffer = [0u8; PAGE_SIZE];
        {
            let mut page = HeapPage::new_with_buffer(&mut buffer);
            page.append(b"hello").unwrap();
        }
        let view = HeapPage::from_buffer_ref(&buffer);
        assert_eq!(view.get_at_slot(0), Some(&b"hello"[..]));
        assert_eq!(view.len(), 1);
    }
}
