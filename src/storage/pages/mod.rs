mod base_page;
mod btree_page;
mod heap_page;
mod id_entry;
mod superblock_page;

pub(super) use base_page::PAGE_ID_NULL;

pub(super) use btree_page::BtreePage;
pub(super) use heap_page::HeapPage;
pub(super) use superblock_page::SuperblockHeader;
pub(super) use superblock_page::SuperblockPage;

pub(super) use id_entry::FreeEntry;
pub(super) use id_entry::U64Entry;

// NOTE all pages must have their first 8 bytes (u64) unused
// the pager will use this to checksum

pub(crate) mod checksum {
    use xxhash_rust::xxh3;
    use zerocopy::big_endian;

    fn compute(buffer: &[u8]) -> u64 {
        xxh3::xxh3_64(&buffer.as_ref()[8..])
    }

    pub(crate) fn set(buffer: &mut [u8]) {
        let cs = compute(buffer);
        buffer[0..8].copy_from_slice(&big_endian::U64::from(cs).to_bytes());
    }

    pub(crate) fn check(buffer: &mut [u8]) -> bool {
        let read = big_endian::U64::from_bytes(buffer[0..8].try_into().unwrap()).get();
        compute(buffer) == read
    }
}
