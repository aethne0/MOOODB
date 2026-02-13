#![allow(dead_code)]

mod macros;

pub(crate) mod page;

pub(crate) const PAGE_SIZE: usize = 0x100;
pub(crate) const PAGE_HEADER_SIZE: usize = 0x40;
pub(crate) use page::Page;

pub(crate) trait ByteOrder: Copy {
    fn from_be(self) -> Self;
    fn to_be(self) -> Self;
}

#[cfg(test)]
mod test {
    use crate::page::{Page, PAGE_SIZE};

    #[test]
    fn test_val_write_read() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut c = Page::from_buffer(1, &mut buffer);

        // aligned u64
        let val = 0x1234abcd98765432u64;
        let off = 0;
        c.write_value(off, val);
        let read_val: u64 = c.read_value(off);
        assert_eq!(read_val, val);

        // unaligned u64
        let val = 0x1234abcd98765432u64;
        let off = 9;
        c.write_value(off, val);
        let read_val: u64 = c.read_value(off);
        assert_eq!(read_val, val);

        // u16
        let val = 0x1234u16;
        let off = 16;
        c.write_value(off, val);
        let read_val: u16 = c.read_value(off);
        assert_eq!(read_val, val);
    }
}
