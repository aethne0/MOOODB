use super::PAGE_SIZE;
use super::serialization::Serialized;
use super::serialization::SerializedU32;
use super::serialization::SerializedU64;

pub(super) const PAGE_HEADER_SIZE: u16 = 0x20;
pub(super) const SLOT_SIZE: u16 = 2 * size_of::<u16>() as u16;
pub(super) const SLOT_IDX_NULL: u16 = u16::MAX;
pub(super) const END_OF_PAGE: u16 = PAGE_SIZE as u16 - 1;

/// The first 24 bytes of every page on disk, regardless of page type.
///
/// Layout (all big-endian):
/// ```text
/// offset  0 | checksum   u32
/// offset  4 | dbg_pad    [u8;4]
/// offset  8 | txid       u64
/// offset 16 | pgid       u64
/// ```
#[derive(Clone)]
#[repr(C)]
pub(super) struct PagePrefix {
    pub(super) checksum: SerializedU32,
    pub(super) dbg_pad:  [u8; 4],
    pub(super) txid:     SerializedU64,
    pub(super) pgid:     SerializedU64,
}
unsafe impl Serialized for PagePrefix {}

impl PagePrefix {
    pub(super) fn new(pgid: u64, checksum: u32, tx_id: u64) -> Self {
        Self {
            checksum: checksum.into(),
            dbg_pad:  *b"SUPA",
            pgid:     pgid.into(),
            txid:     tx_id.into(),
        }
    }
}
