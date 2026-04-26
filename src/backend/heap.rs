use super::page_heap::HeapPage;
use super::storage_manager::*;
use super::PagerErr;
use crate::mooo_assert;

/// It is the responsibility of the caller to update anything that may point to this `root_pgid`
pub(crate) struct Heap {
    pgid: u64,
}
impl Heap {
    // ------------ Constructors, Accessors --------------------------------------------------------

    /// For opening an EXISTING heap
    #[must_use]
    pub(crate) fn new_from_pgid(pgid: u64) -> Self {
        Self { pgid }
    }

    #[must_use]
    pub(crate) fn new<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        tx: &mut R,
    ) -> Result<Heap, PagerErr> {
        let whdl = tx.get_page_alloc()?;
        let pgid = whdl.get_pgid();
        HeapPage::new_with_buffer(whdl.buf);
        Ok(Self::new_from_pgid(pgid))
    }

    pub(crate) fn get_root_pgid(&self) -> u64 {
        self.pgid
    }

    // ------------ Insert -------------------------------------------------------------------------

    pub(crate) fn get<'tx, R: PageReader<'tx>>(
        &self, tx: &R, slot_idx: u16, buf: &mut [u8],
    ) -> Result<Option<usize>, PagerErr> {
        let page = HeapPage::from_buffer_ref(tx.get_page_read(self.pgid)?.buf);
        match page.get_at_slot(slot_idx) {
            Some(entry) => {
                mooo_assert!(entry.len() <= buf.len());
                buf[0..entry.len()].copy_from_slice(entry);
                Ok(Some(entry.len()))
            }
            None => Ok(None),
        }
    }

    // ------------ Insert -------------------------------------------------------------------------

    pub(crate) fn insert<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, val: &[u8],
    ) -> Result<Option<u16>, PagerErr> {
        let whdl = tx.get_page_write(self.pgid)?;
        // todo page leak - see comment at top of btree.rs
        let mut page = HeapPage::from_buffer(whdl.buf);
        let slot_opt = page.append(val);

        self.pgid = whdl.get_pgid();
        Ok(slot_opt)
    }

    // ------------ Delete -------------------------------------------------------------------------

    pub(crate) fn delete<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, slot_idx: u16,
    ) -> Result<(), PagerErr> {
        let whdl = tx.get_page_write(self.pgid)?;
        // TODO page leak - see comment at top of btree.rs
        let mut page = HeapPage::from_buffer(whdl.buf);
        let slot_opt = page.delete_slot_entry(slot_idx);

        self.pgid = whdl.get_pgid();
        Ok(slot_opt)
    }
}
