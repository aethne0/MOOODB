use crate::mooo_assert;

use super::hash_u64_modulo;
use super::serialization::*;
use super::PAGE_SIZE;

#[derive(Clone)]
#[repr(C)]
pub(super) struct SuperblockHeader {
    pub(super) prefix:         PagePrefix,
    pub(super) pgid_bump_next: SerializedU64,
    pub(super) pgid_freelist:  SerializedU64,
    pub(super) pgid_catalog:   SerializedU64,
    pub(super) page_size:      SerializedU16,
}

pub(super) const PGTYPE_SUPERBLOCK: SerializedU64 = SerializedU64(*b"\0SupaBlk");

unsafe impl Serialized for SuperblockHeader {}

impl std::ops::Deref for SuperblockHeader {
    type Target = PagePrefix;
    fn deref(&self) -> &PagePrefix {
        &self.prefix
    }
}
impl std::ops::DerefMut for SuperblockHeader {
    fn deref_mut(&mut self) -> &mut PagePrefix {
        &mut self.prefix
    }
}

const ART_SIZE: usize = 128;
// Indices 0–3: cow variants selected by pgid % 4. Index 4: rare frog (pgid % 256 == 57).
// Each entry is 4 rows × 32 bytes, written to buf[0x80..0x100].
#[rustfmt::skip]
static COWS_AND_SUCH: [[u8; ART_SIZE]; 5] = [
    *b"MOOODB SUPERBLOCK!      ^__^    \
       ~                       (00)\\___\
       ~                       (__)\\   \
       ~                            ||-",
    *b"MOOODB SUPERBLOCK!      ^__^    \
       ~                       (oo)\\___\
       ~                       (__)\\   \
       ~                        u   ||-",
    *b"MOOODB SUPERBLOCK!      ^__^    \
       ~                       (oo)\\___\
       ~                       (__)\\   \
       ~                            ||-",
    *b"MOOODB SUPERBLOCK!      ^__^    \
       ~                       (OO)\\___\
       ~                       (__)\\   \
       ~                         U  ||-",
    *b"FROGDB SUPERBLOCK???            \
       ~   .-(0o      rare     oO)-.   \
       ~  /_  __\\    frog     /__  _\\  \
       ~ |  )/  /   event...  \\  \\(  | ",
];

/// Does not compute checksum
pub(super) fn copy_superblock_to_page(buf: &mut [u8; PAGE_SIZE], sb_header: &SuperblockHeader) {
    mooo_assert!(PAGE_SIZE - size_of::<SuperblockHeader>() >= ART_SIZE);
    sb_header.write_to_prefix(buf);
    buf[size_of::<SuperblockHeader>()..PAGE_SIZE - ART_SIZE].fill(0);
    // insanely high performance branchless cow ascii art writer
    let id = sb_header.txid.get();
    let is_frog = (hash_u64_modulo(id, 256) == 57) as usize;
    let cow_index = hash_u64_modulo(id, 4) as usize;
    let index = cow_index * (1 - is_frog) + 4 * is_frog;
    // writes to end of page
    buf[PAGE_SIZE - ART_SIZE..].copy_from_slice(&COWS_AND_SUCH[index]);
}
