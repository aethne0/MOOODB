use std::ops::{Bound, RangeBounds};

pub(crate) const PAGE_SIZE: usize = 0x100;
const _: () = assert!(PAGE_SIZE <= u16::MAX as usize);

pub(crate) const SLOT_SIZE: u16 = size_of::<u16>() as u16;
const END_OF_PAGE: u16 = (PAGE_SIZE - 1) as u16;
const PAGE_HEADER_SIZE: u16 = 0x40;

mod page_common;
mod page_heap;
mod page_sorted;

pub(crate) use page_common::PageCommon;
pub(crate) use page_heap::PageHeap;
pub(crate) use page_sorted::PageSorted;

pub trait RangeExt<T> {
    fn as_usizes(self) -> (Bound<usize>, Bound<usize>);
}

impl<T, R> RangeExt<T> for R
where
    T: Into<usize> + Copy,
    R: RangeBounds<T>,
{
    #[inline(always)]
    fn as_usizes(self) -> (Bound<usize>, Bound<usize>) {
        let start = match self.start_bound() {
            Bound::Included(&t) => Bound::Included(t.into()),
            Bound::Excluded(&t) => Bound::Excluded(t.into()),
            Bound::Unbounded => Bound::Unbounded,
        };

        let end = match self.end_bound() {
            Bound::Included(&t) => Bound::Included(t.into()),
            Bound::Excluded(&t) => Bound::Excluded(t.into()),
            Bound::Unbounded => Bound::Unbounded,
        };

        (start, end)
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PageType {
    Free = 0x0,
    Leaf = 0x1,
    Inner = 0x2,
    Heap = 0x3,
}
