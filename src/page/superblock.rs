use xxhash_rust::xxh3;

use crate::{
    accessors,
    page::{PAGE_SIZE, PAGE_SIZE_MIN},
    page_fields,
};

/// Fixed-layout page stored at page ID 0. Holds global storage metadata.
///
/// Unlike other page types, `PageSuperblock` owns its buffer (`Box`) rather than
/// borrowing it. It is not a slotted page and has no slot machinery — fields are
/// read and written at fixed byte offsets.
///
/// Layout (all fields big-endian `u64`):
/// ```text
/// 0x00  checksum       — xxh3-64 over bytes [0x08..]
/// 0x08  free_list_root — page ID of the first free-list heap page (0 = none)
/// 0x10  next_page_id   — high-water mark; next page ID to allocate
/// ```
pub(crate) struct PageSuperblock<'buffer> {
    pub(crate) raw: &'buffer mut [u8; PAGE_SIZE],
}

pub(crate) const SUPERBLOCK_PAGE_ID: u64 = 0;

impl<'buffer> PageSuperblock<'buffer> {
    accessors!(u64);

    #[rustfmt::skip]
    page_fields! {
        checksum,           u64, 0x00;
        free_list_next,     u64, 0x08;
        free_list_count,    u64, 0x10;
        next_page_id,       u64, 0x18;
    }

    /// Takes ownership of `buffer` and wraps it as a `PageSuperblock`.
    /// Does not initialize or validate any fields — call [`initialize`] for a fresh
    /// database or read the fields directly after loading from disk.
    ///
    /// [`initialize`]: PageSuperblock::initialize
    pub(crate) fn from_buffer(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }

    /// Computes the xxh3-64 checksum over bytes `[0x08..]` (everything after the checksum field).
    /// Does not write the result — call [`set_checksum`] to persist it.
    ///
    /// [`set_checksum`]: PageSuperblock::set_checksum
    pub(crate) fn compute_checksum(&self) -> u64 {
        xxh3::xxh3_64(&self.raw[8..]) // 8.. because we dont want to checksum the checksum
    }

    /// Initializes the superblock for a freshly created database.
    ///
    /// - `free_list_root` → `0` (no free list yet)
    /// - `next_page_id`   → `1` (page 0 is the superblock itself)
    ///
    /// Also writes a human-readable banner into the tail of the page and
    /// computes and stores the initial checksum.
    pub(crate) fn initialize(&mut self) {
        self.set_free_list_next(0);
        self.set_free_list_count(0);
        self.set_next_page_id(1);

        const START: usize = PAGE_SIZE_MIN / 2;
        const MSG: &'static [u8] = b"Welcome, citizen. Welcome, to MOOODB.\
            This is a superblock, and I hope you enjoy it.";
        self.raw[START..START + MSG.len()].copy_from_slice(MSG);

        let checksum = self.compute_checksum();
        self.set_checksum(checksum);
    }
}
