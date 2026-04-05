use std::ops::{Bound, RangeBounds};

pub(crate) const PAGE_SIZE: usize = 0x1000;

pub(crate) const PAGE_SIZE_MIN: usize = 0x100;
const _: () = assert!(PAGE_SIZE <= u16::MAX as usize);
const _: () = assert!(PAGE_SIZE >= PAGE_SIZE_MIN);

pub(crate) const SLOT_SIZE: u16 = size_of::<u16>() as u16;
const END_OF_PAGE: u16 = (PAGE_SIZE - 1) as u16;
const PAGE_HEADER_SIZE: u16 = 0x40;

mod macros;

mod common;
mod heap;
mod sorted;
mod superblock;

pub(crate) use common::Common;
pub(crate) use heap::Heap;
pub(crate) use sorted::Sorted;
pub(crate) use superblock::SUPERBLOCK_PAGE_ID;
pub(crate) use superblock::Superblock;

/// Converts a range whose bounds implement `Into<usize>` into a plain `(Bound<usize>, Bound<usize>)`,
/// making it usable as a slice index on `[u8]` buffers.
pub trait RangeExt<T> {
    fn as_usizes(self) -> (Bound<usize>, Bound<usize>);
}

impl<T, R> RangeExt<T> for R
where
    T: Into<usize> + Copy,
    R: RangeBounds<T>,
{
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

/// Discriminant stored in the `page_type` header field.
///
/// `Free` pages are unallocated. `Leaf` and `Inner` are B-tree nodes used by
/// [`PageSorted`]. `Heap` pages hold unordered variable-length records via [`PageHeap`].
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PageType {
    Free = 0x0,
    Leaf = 0x1,
    Inner = 0x2,
    Heap = 0x3,
}
