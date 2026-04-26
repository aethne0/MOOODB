//! .▄▄ · ▄▄▄▄▄      ▄▄▄   ▄▄▄·  ▄▄ • ▄▄▄ .
//! ▐█ ▀. •██  ▪     ▀▄ █·▐█ ▀█ ▐█ ▀ ▪▀▄.▀·
//! ▄▀▀▀█▄ ▐█.▪ ▄█▀▄ ▐▀▀▄ ▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄
//! ▐█▄▪▐█ ▐█▌·▐█▌.▐▌▐█•█▌▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌
//!  ▀▀▀▀  ▀▀▀  ▀█▄▀▪.▀  ▀ ▀  ▀ ·▀▀▀▀  ▀▀▀
mod btree;
mod frame_latch;
mod heap;
mod page_btree;
mod page_heap;
mod page_superblock;
mod serialization;
mod storage_manager;

#[cfg(test)]
mod test;

use xxhash_rust::xxh3::xxh3_64;

use crate::mooo_assert;
pub(crate) use page_btree::BTREE_KEY_MAX_LEN;
pub(crate) use storage_manager::*;

/// PAGE_SIZE maybe be inclusively from 256-32KiB, and must be a power of two
const PAGE_SIZE: usize = 0x100;
const _: () = mooo_assert!(
    false
        || PAGE_SIZE == 0x100
        || PAGE_SIZE == 0x200
        || PAGE_SIZE == 0x400
        || PAGE_SIZE == 0x800
        || PAGE_SIZE == 0x1000
        || PAGE_SIZE == 0x2000
        || PAGE_SIZE == 0x4000
        || PAGE_SIZE == 0x8000
);

const PGID_NULL: u64 = u64::MAX;
const fn pgid_valid(pgid: u64) -> bool {
    const _PGID_MAX: u64 = (1 << 48) - 1;
    pgid <= _PGID_MAX
}

// i dont understand any of this

/// MurmurHash3
const fn hash_u64_modulo(mut pgid: u64, modulo: usize) -> usize {
    mooo_assert!(modulo & (modulo - 1) == 0, "modulo must be power of 2");
    pgid ^= pgid >> 33;
    pgid = pgid.wrapping_mul(0xff51_afd7_ed55_8ccd);
    pgid ^= pgid >> 33;
    pgid = pgid.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    pgid ^= pgid >> 33;
    (pgid as usize) & (modulo - 1)
}

/// crc32c
fn compute_checksum(bytes: &[u8]) -> u64 {
    xxh3_64(bytes)
}
