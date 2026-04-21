use std::mem::MaybeUninit;

use super::page_base::U64Entry;
use super::page_btree::BtreePage;
use super::pager::*;
use super::PagerErr;
use super::PAGE_ID_NULL;

struct Btree(u64);

// ------------ Get ----------------------------------------------------------------------------
impl Btree {
    #[must_use]
    pub(crate) fn from_root_id(root_page_id: u64) -> Self {
        Self(root_page_id)
    }

    pub(crate) fn root_id(&self) -> u64 {
        self.0
    }

    pub(crate) fn get<'tx, R: PgRdr<'tx>>(
        &self, handle: &R, key: &[u8],
    ) -> Result<Option<U64Entry>, PagerErr> {
        let mut page_id = self.0;

        loop {
            let page = BtreePage::from_buffer_ref(handle.get_page_read(page_id)?.buf);

            if page.is_leaf() {
                return Ok(page.get(key));
            }

            page_id = page.get_first_slot_ge_key(key).unwrap().get();
        }
    }

    // ------------ New ----------------------------------------------------------------------------
    pub(crate) fn new<'tx, R: PgRdr<'tx> + PgAlloc<'tx>>(tx: &R) -> Result<Btree, PagerErr> {
        let w_hdl = tx.get_page_alloc()?;
        let page_id = w_hdl.get_page_id();
        BtreePage::new_with_buffer(w_hdl.buf, PAGE_ID_NULL, PAGE_ID_NULL);
        Ok(Self::from_root_id(page_id))
    }

    // ------------ Insert -------------------------------------------------------------------------
    pub(crate) fn insert<'tx, R: PgRdr<'tx> + PgAlloc<'tx>>(
        &mut self, tx: &R, key: &[u8], value: U64Entry,
    ) -> Result<(), PagerErr> {
        let mut new_root_page_id = self.0;
        let mut next_page_id = self.0;
        let mut page_stack = PageStack::new();

        loop {
            let w_hdl = tx.get_page_write(next_page_id)?;
            let page_id = w_hdl.get_page_id();
            let mut page = BtreePage::from_buffer(w_hdl.buf);

            if page_stack.len() == 0 {
                // update root_id with the first page we touch (top)
                new_root_page_id = page_id;
            }

            if page.is_leaf() {
                // page.page_id.set(page_id);
                let had_space = page.insert(key, value);
                if !had_space {
                    let right_w_hdl = tx.get_page_alloc()?;
                    let right_page_id = right_w_hdl.get_page_id();
                    page.next_id = right_page_id.into();
                    let right_page =
                        BtreePage::new_with_buffer(right_w_hdl.buf, right_page_id, 555);
                }

                break;
            } else {
                next_page_id = page.get_first_slot_ge_key(key).unwrap().get(); // todo
                page_stack.push(page_id);
            }
        }

        let mut prev_page_id = PAGE_ID_NULL;
        for page_id in page_stack {
            let w_hdl = tx.get_page_write(page_id)?;
            let found_page_id = w_hdl.get_page_id();
            assert!(page_id == found_page_id, "new pages should already be allocated");
            let mut page = BtreePage::from_buffer(w_hdl.buf);
            page.parent_id.set(prev_page_id);
            prev_page_id = page_id;
        }

        self.0 = new_root_page_id;
        Ok(())
    }

    // ------------ Delete -------------------------------------------------------------------------
    // pub(crate) fn delete( key: &[u8]) -> U64Entry {
    //     todo!()
    // }
}

// -------------------------------------------------------------------------------------------------
// *            Page traversal list                                                                *
// -------------------------------------------------------------------------------------------------

const STACK_SIZE: usize = 16;
struct PageStack {
    arr:   [MaybeUninit<u64>; STACK_SIZE],
    front: usize,
    head:  usize,
}

impl PageStack {
    fn new() -> Self {
        Self { arr: [const { MaybeUninit::uninit() }; STACK_SIZE], front: 0, head: 0 }
    }

    fn push(&mut self, item: u64) {
        assert!(self.head < STACK_SIZE);
        self.arr[self.head] = MaybeUninit::new(item);
        self.head += 1;
    }

    fn len(&self) -> usize {
        self.head
    }
}

impl Iterator for PageStack {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front == self.head {
            return None;
        }
        let i = self.front;
        self.front += 1;
        Some(unsafe { std::mem::replace(&mut self.arr[i], MaybeUninit::uninit()).assume_init() })
    }
}

// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod test {

    use std::sync::atomic::AtomicUsize;

    use crate::sync;

    use super::*;

    #[test]
    fn btree_inserts() {
        let file = tempfile::tempfile().unwrap();
        let mgr = Pager::new(64, file);

        let w_tx = mgr.write_tx();

        let mut btree = Btree::new(&w_tx).unwrap();
        let root_id = btree.root_id();
        btree.insert(&w_tx, b"asd", 0xab.into()).unwrap();
        btree.insert(&w_tx, b"zxc", 0xbc.into()).unwrap();
        btree.insert(&w_tx, b"rewt", 0xde.into()).unwrap();

        w_tx.commit(Durability::Flush).unwrap();

        let r_tx = mgr.read_tx();

        let res = btree.get(&r_tx, b"rewt").unwrap();
        assert!(res.is_some_and(|val| val.get() == 0xde));

        let w_tx = mgr.write_tx();

        let mut btree = Btree::from_root_id(root_id);
        btree.insert(&w_tx, b"xxx", 0x12.into()).unwrap();
        btree.insert(&w_tx, b"zxc", 0x55.into()).unwrap();
        btree.insert(&w_tx, b"rewz", 0x77.into()).unwrap();

        w_tx.commit(Durability::Flush).unwrap();
    }

    #[test]
    fn btree_inserts_threads() {
        let file = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open("/xblk/test/test.moo")
            .unwrap();
        let mgr = Pager::new(64, file);

        eprintln!("");
        static CTR: AtomicUsize = AtomicUsize::new(0);

        sync::thread::scope(|s| {
            for _ in 0..8 {
                s.spawn(|| {
                    let id = CTR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let w_tx = mgr.write_tx();
                    eprintln!("t{} -> 1", id);

                    let mut btree = Btree::new(&w_tx).unwrap();
                    let root_page_id = btree.root_id();
                    eprintln!("t{} -> 1 root_page_id {}", id, root_page_id);
                    btree.insert(&w_tx, b"asd", 0xab.into()).unwrap();
                    btree.insert(&w_tx, b"zxc", 0xbc.into()).unwrap();
                    btree.insert(&w_tx, b"rewt", 0xde.into()).unwrap();

                    w_tx.commit(Durability::Flush).unwrap();

                    let r_tx = mgr.read_tx();

                    let res = btree.get(&r_tx, b"rewt").unwrap();
                    assert!(res.is_some_and(|val| val.get() == 0xde));

                    let w_tx = mgr.write_tx();
                    eprintln!("t{} -> 2", id);

                    let mut btree = Btree::from_root_id(root_page_id);
                    btree.insert(&w_tx, b"xxx", 0x12.into()).unwrap();
                    btree.insert(&w_tx, b"zxc", 0x55.into()).unwrap();
                    btree.insert(&w_tx, b"rewz", 0x77.into()).unwrap();

                    eprintln!("t{} -> 2 root_page_id {}", id, btree.root_id());

                    w_tx.commit(Durability::Flush).unwrap();
                });
            }
        });

        CTR.store(0, std::sync::atomic::Ordering::Relaxed);
        sync::thread::scope(|s| {
            for _ in 0..8 {
                s.spawn(|| {
                    let id = CTR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let w_tx = mgr.write_tx();

                    let mut btree = Btree::from_root_id(id as u64 % 2 + 2);
                    btree.insert(&w_tx, b"xxx", 0x13.into()).unwrap();
                    btree.insert(&w_tx, b"zxc", 0x56.into()).unwrap();
                    btree.insert(&w_tx, b"rewz", 0x88.into()).unwrap();

                    w_tx.commit(Durability::Flush).unwrap();
                });
            }
        });
    }
}
