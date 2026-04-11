mod base_page;
mod btree_page;
mod heap_page;
mod id_entry;
mod superblock_page;

pub(super) use base_page::PAGE_ID_NULL;
pub(super) use base_page::PagePrefix;

pub(super) use btree_page::BtreePage;
pub(super) use heap_page::HeapPage;
pub(super) use superblock_page::SuperblockHeader;
pub(super) use superblock_page::SuperblockPage;

pub(super) use id_entry::FreeEntry;
pub(super) use id_entry::U64Entry;

pub(crate) mod checksum {
    use super::PagePrefix;
    use std::mem::offset_of;
    use xxhash_rust::xxh3;
    use zerocopy::FromBytes;

    fn compute(buffer: &[u8]) -> u64 {
        // hash everything after the checksum field
        xxh3::xxh3_64(&buffer[offset_of!(PagePrefix, page_id)..])
    }

    pub(crate) fn set(buffer: &mut [u8]) {
        let cs = compute(buffer);
        let prefix = PagePrefix::mut_from_prefix(buffer).unwrap().0;
        prefix.checksum.set(cs);
    }

    pub(crate) fn check(buffer: &[u8]) -> bool {
        let prefix = PagePrefix::ref_from_prefix(buffer).unwrap().0;
        compute(buffer) == prefix.checksum.get()
    }
}
