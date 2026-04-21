//! .▄▄ · ▄▄▄▄▄      ▄▄▄   ▄▄▄·  ▄▄ • ▄▄▄ .
//! ▐█ ▀. •██  ▪     ▀▄ █·▐█ ▀█ ▐█ ▀ ▪▀▄.▀·
//! ▄▀▀▀█▄ ▐█.▪ ▄█▀▄ ▐▀▀▄ ▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄
//! ▐█▄▪▐█ ▐█▌·▐█▌.▐▌▐█•█▌▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌
//!  ▀▀▀▀  ▀▀▀  ▀█▄▀▪.▀  ▀ ▀  ▀ ·▀▀▀▀  ▀▀▀
mod page_base;
mod page_btree;
mod page_heap;
mod page_superblock;
mod serialization;

mod btree;
mod heap;
mod manager;
mod pager;

#[cfg(test)]
mod test;

use crate::mooo_assert;
pub(crate) use page_btree::BTREE_KEY_MAX_LEN;
use pager::*;

const PAGE_SIZE: usize = 256;
const PGID_NULL: u64 = u64::MAX;

const fn pgid_valid(pgid: u64) -> bool {
    const _PGID_MAX: u64 = (1 << 48) - 1;
    pgid <= _PGID_MAX
}

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
const fn compute_checksum(bytes: &[u8]) -> u32 {
    const _CRC32C_TABLE: [u32; 256] = {
        let mut table = [0u32; 256];
        let mut i = 0;
        while i < 256 {
            let mut crc = i as u32;
            let mut j = 0;
            while j < 8 {
                if crc & 1 != 0 {
                    crc = (crc >> 1) ^ 0x82f6_3b78;
                } else {
                    crc >>= 1;
                }
                j += 1;
            }
            table[i] = crc;
            i += 1;
        }
        table
    };

    let mut crc: u32 = 0xffff_ffff;
    let mut i = 0;
    while i < bytes.len() {
        let idx = ((crc ^ bytes[i] as u32) & 0xff) as usize;
        crc = (crc >> 8) ^ _CRC32C_TABLE[idx];
        i += 1;
    }
    crc ^ 0xffff_ffff
}
