use xxhash_rust::xxh3;

use crate::{
    accessors,
    page::{PAGE_SIZE, PAGE_SIZE_MIN},
    page_fields,
};

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

    pub(crate) fn from_buffer(buffer: &'buffer mut [u8; PAGE_SIZE]) -> Self {
        Self { raw: buffer }
    }

    pub(crate) fn compute_checksum(&self) -> u64 {
        xxh3::xxh3_64(&self.raw[8..]) // 8.. because we dont want to checksum the checksum
    }

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
