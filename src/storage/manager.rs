use crate::mooo_assert;

use super::pgid_valid;
use super::serialization::Serialized;
use super::serialization::SerializedU64;

/// Note: we will keep a page-table btree that translates logical row-ids to physical heap-ids,
/// whenever a heap page is CoW shadowed we need to also update that page-table btree
/// holy write amplification!
pub(super) struct StorageManager{}

// -------------------------------------------------------------------------------------------------
// *            Definitions                                                                        *
// -------------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct FreeEntry {
    txid: SerializedU64,
    pgid: SerializedU64,
}
unsafe impl Serialized for FreeEntry {}

/// most-significant 48 bits are pgid, lower are slot
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub(super) struct HeapPtr(SerializedU64);
impl HeapPtr {
    pub(super) fn new(pgid: u64, slot_idx: u16) -> Self {
        mooo_assert!(pgid_valid(pgid));
        let val = (pgid << 16) | (slot_idx as u64);
        Self(val.into())
    }

    pub(super) fn set_pgid(&mut self, pgid: u64) {
        mooo_assert!(pgid_valid(pgid));
        self.0 = ((pgid << 16) | (self.0.get() & 0xffff)).into();
    }

    pub(super) fn set_slot(&mut self, slot_idx: u16) {
        self.0 = ((self.0.get() & 0xffff_ffff_ffff_0000) | (slot_idx as u64)).into();
    }

    pub(super) fn pgid(&self) -> u64 {
        (self.0.get() & 0xffff_ffff_ffff_0000) >> 16
    }

    pub(super) fn slot(&self) -> u16 {
        (self.0.get() & 0xffff) as u16
    }
}
unsafe impl Serialized for HeapPtr {}
impl From<SerializedU64> for HeapPtr {
    fn from(value: SerializedU64) -> Self {
        HeapPtr(value)
    }
}
impl Into<SerializedU64> for HeapPtr {
    fn into(self) -> SerializedU64 {
        self.0
    }
}
