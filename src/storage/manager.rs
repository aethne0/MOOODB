use super::PageWriter;
use super::Pager;
use super::ReadTxHdl;
use super::WrHdl;
use super::WriteTxHdlBump;
use super::pgid_valid;
use super::serialization::Serialized;
use super::serialization::SerializedU64;
use crate::mooo_assert;
use crate::storage::PGID_NULL;
use crate::storage::pager::PagerErr;

/// Note: we will keep a page-table btree that translates logical row-ids to physical heap-ids,
/// whenever a heap page is CoW shadowed we need to also update that page-table btree
/// holy write amplification!
pub(super) struct StorageManager {
    pager: Pager,
}

impl StorageManager {
    #[must_use]
    pub(super) fn new(pager: Pager) -> Self {
        Self { pager }
    }

    #[must_use = "RAII ReadTxHdl releases when dropped"]
    pub(super) fn read_tx<'tx>(&'tx self) -> ReadTxHdl<'tx> {
        self.pager.read_tx()
    }

    #[must_use = "RAII ReadTxHdl releases when dropped"]
    pub(super) fn write_tx<'tx>(&'tx self) -> WriteTxHdlMgr<'tx> {
        let bump_tx = self.pager.write_tx();
        WriteTxHdlMgr { tx: bump_tx }
    }
}

pub(super) struct WriteTxHdlMgr<'tx> {
    /// Inner bump-alloc write tx
    tx: WriteTxHdlBump<'tx>,
}

impl<'tx> PageWriter<'tx> for WriteTxHdlMgr<'tx> {
    fn update_catalog_root_id(&self, pgid: u64) {
        self.tx.update_catalog_root_id(pgid);
    }

    fn get_page_alloc(&self) -> Result<WrHdl<'tx>, PagerErr> {
        let inner = self.tx.inner.borrow_mut();
        let free_list_pgid = inner.superblock.alloc_free_head_pgid.get();
        if free_list_pgid != PGID_NULL {
            todo!()
        } else {
            drop(inner);
            self.tx.get_page_alloc()
        }
    }

    fn get_page_write(&self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr> {
        // must free TODO
        self.tx.get_page_write(pgid)
    }
}

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
