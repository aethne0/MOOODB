// TODO we need some way mark claimed pages as de-claimed, if we end up aborting something see:
// Btree::pop_min_lt
//
// TODO btree has large stack allocations
//
// TODO btree delete rebalancing
//
// TODO key-only freelist btree
//
// TODO page leaks on early return - maybe we should call commit or something on CoW shadowed pages
// er wait no i dont think it matters... cause we will just recover the old superblock unless we
// keep doing stuff with the same wtx...
//
// `pop_min_lt`: TODO this is CoWing even if we dont make a change,
//
// TODO we can optimze `get_index` and `len` by keeping an entry count on inner pages, which should
// be roughly free to maintain because of CoW
//
// TODO obviously for the freelist index thing we should just be keeping a cursor/iterator

use std::cell::Ref;
use std::cell::RefCell;
use std::cell::RefMut;
use std::mem::MaybeUninit;

use super::page_btree::BtreePage;
use super::page_btree::BtreePageType;
use super::serialization::*;
use super::storage_manager::*;
use super::PagerErr;
use crate::mooo_assert;

/// NOTE It is the responsibility of the caller to update anything that points to `root_pgid`
pub(crate) struct Btree {
    root_pgid: u64,
}

impl Btree {
    // ------------ Constructors, Accessors --------------------------------------------------------

    /// For opening an EXISTING btree
    #[must_use]
    pub(crate) fn from_pgid(root_pgid: u64) -> Self {
        Self { root_pgid }
    }

    #[must_use]
    pub(crate) fn new<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        tx: &mut R,
    ) -> Result<Btree, PagerErr> {
        let whdl = tx.get_page_alloc()?;
        let pgid = whdl.get_pgid();
        BtreePage::new_with_buffer(whdl.buf, BtreePageType::Leaf);
        Ok(Self::from_pgid(pgid))
    }

    pub(crate) fn get_root_pgid(&self) -> u64 {
        self.root_pgid
    }

    // ------------ Util ---------------------------------------------------------------------------

    fn traverse<'tx, R: PageReader<'tx>>(
        &mut self, tx: &R, key: &[u8],
    ) -> Result<Traversal<RdHdl<'tx>>, PagerErr> {
        let mut traversal = Traversal::<RdHdl<'_>>::new();
        let mut next_pgid = self.root_pgid;

        loop {
            let rhdl = tx.get_page_read(next_pgid)?;

            let curr_page = BtreePage::from_buffer_ref(rhdl.buf);

            match curr_page.get_page_type() {
                BtreePageType::Inner => {
                    let (pgid_entry, slot) = curr_page.get_traversal_next_page(key).unwrap();
                    next_pgid = pgid_entry.get();
                    traversal.push((rhdl, slot));
                }
                BtreePageType::Leaf => {
                    traversal.push((rhdl, SLOT_INDEX_NULL));
                    break;
                }
            }
        }

        Ok(traversal)
    }

    fn traverse_cow<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8],
    ) -> Result<Traversal<WrHdl<'tx>>, PagerErr> {
        let mut traversal = Traversal::<WrHdl<'_>>::new();
        let mut next_pgid = self.root_pgid;

        loop {
            let whdl = tx.get_page_write(next_pgid)?;

            if traversal.len() > 0 {
                // fix parent_ptr
                let (mut parent_whdl, slot_index) = traversal.last_mut();
                let mut parent_page = BtreePage::from_buffer(parent_whdl.buf);
                parent_page.overwrite_value_with_slot_index(slot_index, whdl.get_pgid().into());
            }

            let curr_page = BtreePage::from_buffer(whdl.buf);

            match curr_page.get_page_type() {
                BtreePageType::Inner => {
                    let (pgid_entry, slot) = curr_page.get_traversal_next_page(key).unwrap();
                    next_pgid = pgid_entry.get();
                    traversal.push((whdl, slot));
                }
                BtreePageType::Leaf => {
                    traversal.push((whdl, SLOT_INDEX_NULL));
                    break;
                }
            }
        }

        Ok(traversal)
    }

    // ------------ Accessor methods (read) --------------------------------------------------------

    #[must_use = "this fn has no side effects - why are you calling this?"]
    pub(crate) fn get<'tx, R: PageReader<'tx>>(
        &self, tx: &R, key: &[u8],
    ) -> Result<Option<SerializedU64>, PagerErr> {
        let mut next_pgid = self.root_pgid;

        // not using `traverse`, because theres no need to keep the other pages pinned
        loop {
            let page = BtreePage::from_buffer_ref(tx.get_page_read(next_pgid)?.buf);
            if page.is_leaf() {
                return Ok(page.get(key));
            }
            next_pgid = page.get_traversal_next_page(key).unwrap().0.get();
        }
    }

    #[must_use = "this fn has no side effects - why are you calling this?"]
    pub(crate) fn get_min<'tx, R: PageReader<'tx>>(
        &self, tx: &R,
    ) -> Result<Option<SerializedU64>, PagerErr> {
        let mut next_pgid = self.root_pgid;

        loop {
            let page = BtreePage::from_buffer_ref(tx.get_page_read(next_pgid)?.buf);
            if page.len() == 0 {
                return Ok(None);
            }
            if page.is_leaf() {
                return Ok(Some(page.entry_at_slot(0).1));
            }
            next_pgid = page.entry_at_slot(0).1.get()
        }
    }

    #[must_use = "this fn has no side effects - why are you calling this?"]
    pub(crate) fn get_max<'tx, R: PageReader<'tx>>(
        &self, tx: &R,
    ) -> Result<Option<SerializedU64>, PagerErr> {
        let mut next_pgid = self.root_pgid;

        loop {
            let page = BtreePage::from_buffer_ref(tx.get_page_read(next_pgid)?.buf);
            if page.len() == 0 {
                return Ok(None);
            }
            if page.is_leaf() {
                return Ok(Some(page.entry_at_slot(page.len() - 1).1));
            }
            next_pgid = page.entry_at_slot(page.len() - 1).1.get()
        }
    }

    // TODO replace this with a persistent cursor, so we dont re-traverse every time
    #[must_use = "this fn has no side effects - why are you calling this?"]
    pub(crate) fn freelist_get_index<'tx, R: PageReader<'tx>>(
        &self, tx: &R, index: usize,
    ) -> Result<Option<FreeEntry>, PagerErr> {
        let pgid = self.root_pgid;
        let page = BtreePage::from_buffer_ref(tx.get_page_read(pgid)?.buf);

        if page.is_leaf() {
            if page.len() as usize > index {
                return Ok(Some(FreeEntry::read_from_bytes(page.entry_at_slot(index as u16).0)));
            } else {
                return Ok(None);
            }
        }

        let mut offset = 0;
        for slot_index in 0..page.len() {
            let child_pgid = page.entry_at_slot(slot_index).1.get();
            let child_tree = Btree::from_pgid(child_pgid);
            mooo_assert!(index as isize - offset as isize >= 0);
            let found_opt = child_tree.freelist_get_index(tx, index - offset)?;
            match found_opt {
                None => {
                    offset += child_tree.len(tx)? as usize;
                }
                Some(entry) => return Ok(Some(entry)),
            }
        }

        Ok(None)
    }

    #[must_use = "this fn has no side effects - why are you calling this?"]
    pub(crate) fn len<'tx, R: PageReader<'tx>>(&self, tx: &R) -> Result<usize, PagerErr> {
        let pgid = self.root_pgid;
        let mut count = 0;

        let page = BtreePage::from_buffer_ref(tx.get_page_read(pgid)?.buf);
        if page.is_leaf() {
            return Ok(page.len() as usize);
        }

        for slot_index in 0..page.len() {
            let child_pgid = page.entry_at_slot(slot_index).1.get();
            count += Btree::from_pgid(child_pgid).len(tx)?;
        }

        Ok(count)
    }

    // ------------ Accessor methods (write) -------------------------------------------------------

    pub(crate) fn insert<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8], val: impl Into<SerializedU64>,
    ) -> Result<(), PagerErr> {
        let val = val.into();

        let traversal = self.traverse_cow(tx, key)?;

        let had_space = {
            let (mut leaf, _) = traversal.last_mut();
            let mut curr_page = BtreePage::from_buffer(leaf.buf);
            curr_page.insert(key, val)
        };

        if had_space {
            // if we had space to insert we just are good
            self.root_pgid = traversal.index_ref(0).0.get_pgid();
            return Ok(());
        }

        // we have to split our leaf node

        let (mut left_whdl, _) = traversal.last_mut();
        let mut right_whdl = tx.get_page_alloc()?;
        redistribute(&mut left_whdl, &mut right_whdl, key, val);

        // we have to (maybe) propogate our split

        let mut traversal_index = traversal.len() - 1;
        while traversal_index > 0 {
            // theres a page above us
            // we will decrement our traversal_index and fetch that page

            traversal_index -= 1;
            let (mut parent_whdl, _) = traversal.index_mut(traversal_index);
            let had_space = insert_child_ptr(&mut parent_whdl, &mut right_whdl);

            if had_space {
                drop(parent_whdl);
                self.root_pgid = traversal.index_ref(0).0.get_pgid();
                return Ok(());
            } else {
                let mut right_parent_whdl = tx.get_page_alloc()?;
                redistribute_with_child_ptr(&mut parent_whdl, &mut right_parent_whdl, &right_whdl);
                left_whdl = parent_whdl;
                right_whdl = right_parent_whdl;
            }
        }

        // if we havent returned by now, we need to make a new root, because we split the previous
        // layer which WAS the root

        let mut root_whdl = tx.get_page_alloc()?;
        BtreePage::new_with_buffer(root_whdl.buf, BtreePageType::Inner);
        insert_child_ptr(&mut root_whdl, &mut left_whdl);
        insert_child_ptr(&mut root_whdl, &mut right_whdl);

        self.root_pgid = root_whdl.get_pgid();
        return Ok(());
    }

    pub(crate) fn delete<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8],
    ) -> Result<(), PagerErr> {
        let mut traversal = self.traverse_cow(tx, key)?;
        mooo_assert!(traversal.len() > 0);
        self.root_pgid = traversal.index_ref(0).0.get_pgid();

        // this is a somewhat simplified delete method - we just delete an ntry, and then the only
        // "rebalancing" we do is freeing the page if we are empty, and popping back up to the
        // parent and deleting the entry there (recursively)

        let mut leaf = true;

        // we don't want to remove the root
        loop {
            // repeatedly pop and free empty leaves
            let (whdl, slot) = traversal.pop();
            let mut page = BtreePage::from_buffer(whdl.buf);

            if leaf {
                page.delete(key);
                leaf = false;
            } else {
                page.delete_slot_entry(slot);
            }

            if page.len() > 0 {
                // page still has items, were done
                return Ok(());
            }

            if traversal.len() == 0 {
                // were at the root of our btree, so we don't want to delete anymore
                // this page is empty, though, so we should change it to a leaf, instead of having a
                // top level empty inner node unexpectedly later
                page.set_page_type(BtreePageType::Leaf);
                return Ok(());
            }

            let pgid = whdl.get_pgid();
            drop(whdl);
            tx.free_page(pgid)?;
        }
    }
}

// ------------ Helpers ----------------------------------------------------------------------------

/// these pages should be initialized
fn insert_child_ptr(parent_whdl: &mut WrHdl<'_>, child_whdl: &mut WrHdl<'_>) -> bool {
    // insert split leafs into new root
    let child_pgid = child_whdl.get_pgid();
    let child_page = BtreePage::from_buffer(child_whdl.buf);
    let mut parent_page = BtreePage::from_buffer(parent_whdl.buf);
    parent_page.insert(child_page.entry_at_slot(0).0, child_pgid.into())
}

/// left should be initialized, right should NOT be initiliazed
fn redistribute(
    left_whdl: &mut WrHdl<'_>, right_whdl: &mut WrHdl<'_>, key: &[u8], pk: SerializedU64,
) {
    let mut left = BtreePage::from_buffer(left_whdl.buf);
    let mut right = BtreePage::new_with_buffer(right_whdl.buf, left.get_page_type());
    left.redistribute_into(&mut right);
    if key < right.entry_at_slot(0).0 {
        let _had_space = left.insert(key, pk);
        mooo_assert!(_had_space);
    } else {
        let _had_space = right.insert(key, pk);
        mooo_assert!(_had_space);
    }
}

/// exact same as `redistribute` except it automatically gets key + pk from a `child_whdl` page
fn redistribute_with_child_ptr(
    left_whdl: &mut WrHdl<'_>, right_whdl: &mut WrHdl<'_>, child_whdl: &WrHdl<'_>,
) {
    let child_pgid = child_whdl.get_pgid();
    let child_page = BtreePage::from_buffer_ref(child_whdl.buf);
    redistribute(left_whdl, right_whdl, child_page.entry_at_slot(0).0, child_pgid.into());
}

// ------------ Page traversal list ----------------------------------------------------------------

// const STACK_SIZE: usize = 48;
const STACK_SIZE: usize = 8;
struct Traversal<T> {
    head: usize,
    arr:  [MaybeUninit<(RefCell<T>, u16)>; STACK_SIZE],
}

impl<T> Traversal<T> {
    fn new() -> Self {
        Self { arr: [const { MaybeUninit::uninit() }; STACK_SIZE], head: 0 }
    }

    /// this should be the slot-index in the corresponding WrHdl page's parent
    fn push(&mut self, item: (T, u16)) {
        mooo_assert!(self.head < STACK_SIZE);
        self.arr[self.head] = MaybeUninit::new((RefCell::new(item.0), item.1));
        self.head += 1;
    }

    fn index_ref<'b>(&'b self, index: usize) -> (Ref<'b, T>, u16) {
        mooo_assert!(index < self.head);
        let entry = unsafe { self.arr[index].assume_init_ref() };
        (entry.0.borrow(), entry.1)
    }

    fn index_mut<'b>(&'b self, index: usize) -> (RefMut<'b, T>, u16) {
        mooo_assert!(index < self.head);
        let entry = unsafe { self.arr[index].assume_init_ref() };
        (entry.0.borrow_mut(), entry.1)
    }

    fn last_ref<'b>(&'b self) -> (Ref<'b, T>, u16) {
        self.index_ref(self.head - 1)
    }

    fn last_mut<'b>(&'b self) -> (RefMut<'b, T>, u16) {
        self.index_mut(self.head - 1)
    }

    fn len(&self) -> usize {
        self.head
    }

    fn pop(&mut self) -> (T, u16) {
        mooo_assert!(self.head > 0);
        self.head -= 1;
        let entry = unsafe { self.arr[self.head].assume_init_read() };
        (entry.0.into_inner(), entry.1)
    }

    fn last_slot_mut(&mut self) -> &mut u16 {
        mooo_assert!(self.head > 0);
        &mut unsafe { self.arr[self.head - 1].assume_init_mut() }.1
    }
}

impl<T> Drop for Traversal<T> {
    fn drop(&mut self) {
        for i in 0..self.len() {
            unsafe { self.arr[i].assume_init_drop() };
        }
    }
}
