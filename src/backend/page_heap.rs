use std::ops::Deref;
use std::ops::DerefMut;

use super::serialization::*;
use super::PAGE_SIZE;
use crate::mooo_assert;

#[repr(C)]
pub(super) struct HeapPageHeader {
    pub(super) prefix:     PagePrefix,
    _unused:               [u8; 24],
    pub(super) page_flags: SerializedU16,
    pub(super) upper_ptr:  SerializedU16,
    pub(super) free_bytes: SerializedU16,
    pub(super) lower_ptr:  SerializedU16,
}
const _: () = mooo_assert!(size_of::<HeapPageHeader>() == PAGE_HEADER_SIZE as usize);
unsafe impl Serialized for HeapPageHeader {}

pub(super) struct HeapPage<Buf> {
    raw: Buf,
}

// constructors

impl<'b> HeapPage<&'b mut [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer(buffer: &'b mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }

    pub(super) fn new_with_buffer(buffer: &'b mut [u8; PAGE_SIZE]) -> Self {
        let mut page = Self::from_buffer(buffer);
        page.prefix.meta = *b" Heap\0\0";
        page.reinit_page();
        page
    }
}

impl<'b> HeapPage<&'b [u8; PAGE_SIZE]> {
    pub(super) const fn from_buffer_ref(buffer: &'b [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }
}

// deref to header

impl<Buf: AsRef<[u8]>> Deref for HeapPage<Buf> {
    type Target = HeapPageHeader;

    fn deref(&self) -> &HeapPageHeader {
        HeapPageHeader::ref_from_bytes(&self.raw.as_ref()[..PAGE_HEADER_SIZE as usize])
    }
}

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> DerefMut for HeapPage<Buf> {
    fn deref_mut(&mut self) -> &mut HeapPageHeader {
        HeapPageHeader::mut_from_bytes(&mut self.raw.as_mut()[..PAGE_HEADER_SIZE as usize])
    }
}

// read impl

impl<Buf: AsRef<[u8]>> HeapPage<Buf> {
    fn raw(&self) -> &[u8] {
        self.raw.as_ref()
    }

    fn free_bytes_contig(&self) -> u16 {
        1 + self.lower_ptr.get() - self.upper_ptr.get()
    }

    fn len(&self) -> u16 {
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

    fn val_at_slot(&self, slot_index: u16) -> &[u8] {
        let (offset, len) = self.offset_len_from_slot(slot_index);
        &self.raw()[offset as usize..(offset + len) as usize]
    }

    fn iter(&self) -> SlottedPageIterator<'_, Buf> {
        SlottedPageIterator { page: self, slot_index: 0 }
    }

    pub(super) fn get_at_slot(&self, slot_index: u16) -> Option<&[u8]> {
        if slot_index >= self.len() {
            return None;
        }
        Some(self.val_at_slot(slot_index))
    }
}

// write impl

impl<Buf: AsRef<[u8]> + AsMut<[u8]>> HeapPage<Buf> {
    fn write_slot(&mut self, slot_index: u16, offset: u16, len: u16) {
        let base = (PAGE_HEADER_SIZE + slot_index * SLOT_SIZE) as usize;
        let raw = self.raw.as_mut();
        SerializedU16::from(offset).write_to_prefix(&mut raw[base..]);
        SerializedU16::from(len).write_to_prefix(&mut raw[base + size_of::<u16>()..]);
    }

    fn reinit_page(&mut self) {
        self.upper_ptr = PAGE_HEADER_SIZE.into();
        self.lower_ptr = END_OF_PAGE.into();
        self.free_bytes = (PAGE_SIZE as u16 - PAGE_HEADER_SIZE).into();

        #[cfg(debug_assertions)]
        self.raw.as_mut()[PAGE_HEADER_SIZE as usize..].fill(0);
    }

    pub(super) fn delete_slot_entry(&mut self, slot_index: u16) {
        mooo_assert!(slot_index < self.len());
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

    /// Appends `val` to the page and returns its slot index.
    ///
    /// Triggers compaction automatically if there is not enough contiguous free space.
    /// Returns `None` if the page is full; no changes are made in that case.
    pub(super) fn append(&mut self, val: &[u8]) -> Option<u16> {
        let entry_len = u16::try_from(val.len()).expect("val too long");
        if entry_len + SLOT_SIZE > self.free_bytes.get() {
            return None;
        }
        if self.free_bytes_contig() < entry_len + SLOT_SIZE {
            self.compact();
        }
        let slot_index = self.len();
        let offset = self.lower_ptr.get() - entry_len + 1;
        self.write_slot(slot_index, offset, entry_len);
        self.upper_ptr = (self.upper_ptr.get() + SLOT_SIZE).into();
        self.lower_ptr = (offset - 1).into();
        self.free_bytes = (self.free_bytes.get() - SLOT_SIZE - entry_len).into();
        self.raw.as_mut()[offset as usize..(offset + entry_len) as usize].copy_from_slice(val);
        Some(slot_index)
    }

    /// Defragments the page by rewriting all live entries into a contiguous block.
    fn compact(&mut self) {
        let mut cloned_raw = [0u8; PAGE_SIZE];
        cloned_raw.copy_from_slice(self.raw());
        let cloned_page = HeapPage::from_buffer(&mut cloned_raw);
        self.reinit_page();
        for (_, v) in cloned_page.iter() {
            self.append(v);
        }
    }
}

// iterator

pub(super) struct SlottedPageIterator<'a, Buf: AsRef<[u8]>> {
    page:       &'a HeapPage<Buf>,
    slot_index: u16,
}

impl<'a, B: AsRef<[u8]>> Iterator for SlottedPageIterator<'a, B> {
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

impl<'a, B: AsRef<[u8]>> IntoIterator for &'a HeapPage<B> {
    type Item = (u16, &'a [u8]);
    type IntoIter = SlottedPageIterator<'a, B>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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

        let free_before = page.free_bytes.get();

        for i in (0..page.len()).step_by(2).rev() {
            page.delete_slot_entry(i as u16);
        }

        assert!(page.free_bytes.get() > free_before);
        assert!(page.free_bytes.get() > page.free_bytes_contig());

        page.compact();

        assert_eq!(page.free_bytes.get(), page.free_bytes_contig());

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

        page.reinit_page();
        assert_eq!(page.len(), 0);
        assert_eq!(page.free_bytes.get(), PAGE_SIZE as u16 - PAGE_HEADER_SIZE);
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
