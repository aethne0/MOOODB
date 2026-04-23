use std::cell::Ref;
use std::cell::RefCell;
use std::cell::RefMut;
use std::mem::MaybeUninit;

use super::page_btree::BtreePage;
use super::serialization::*;
use super::storage_manager::*;
use super::PagerErr;
use crate::mooo_assert;
use crate::storage::page_btree::BtreePageType;
use crate::storage::BTREE_KEY_MAX_LEN;

// TODO page leaks on early return - maybe we should call commit or something on CoW shadowed pages
// er wait no i dont think it matters... cause we will just recover the old superblock
// unless we keep doing stuff with the same wtx...

/// It is the responsibility of the caller to update anything that may point to this `root_pgid`
pub(crate) struct Btree {
    root_pgid: u64,
}
impl Btree {
    // ------------ Constructors, Accessors --------------------------------------------------------

    /// For opening an EXISTING btree
    #[must_use]
    pub(crate) fn new_from_root_pgid(root_pgid: u64) -> Self {
        Self { root_pgid }
    }

    #[must_use]
    pub(crate) fn new<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        tx: &mut R,
    ) -> Result<Btree, PagerErr> {
        let whdl = tx.get_page_alloc()?;
        let pgid = whdl.get_pgid();
        BtreePage::new_with_buffer(whdl.buf, BtreePageType::Leaf);
        Ok(Self::new_from_root_pgid(pgid))
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
                    traversal.push((rhdl, SLOT_IDX_NULL));
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

            // fix parent_ptr
            if traversal.len() > 0 {
                let (mut parent_whdl, slot_idx) = traversal.last_mut();
                let mut parent_page = BtreePage::from_buffer(parent_whdl.buf);
                parent_page.overwrite_value_with_slot_index(slot_idx, whdl.get_pgid().into());
            }

            let curr_page = BtreePage::from_buffer(whdl.buf);

            match curr_page.get_page_type() {
                BtreePageType::Inner => {
                    let (pgid_entry, slot) = curr_page.get_traversal_next_page(key).unwrap();
                    next_pgid = pgid_entry.get();
                    traversal.push((whdl, slot));
                }
                BtreePageType::Leaf => {
                    traversal.push((whdl, SLOT_IDX_NULL));
                    break;
                }
            }
        }

        Ok(traversal)
    }

    // ------------ Get ----------------------------------------------------------------------------

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
                // todo - shouldnt be possible once delete is working correctly
                // actually, with a brand new root its possible, nvm maybe
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
                // todo - shouldnt be possible once delete is working correctly
                // actually, with a brand new root its possible, nvm maybe
                return Ok(None);
            }
            if page.is_leaf() {
                return Ok(Some(page.entry_at_slot(page.len() - 1).1));
            }
            next_pgid = page.entry_at_slot(page.len() - 1).1.get()
        }
    }

    // ------------ Insert -------------------------------------------------------------------------

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

        let mut traversal_idx = traversal.len() - 1;
        while traversal_idx > 0 {
            // theres a page above us
            // we will decrement our traversal_idx and fetch that page

            traversal_idx -= 1;
            let (mut parent_whdl, _) = traversal.index_mut(traversal_idx);
            let had_space = insert_child_ptr(&mut parent_whdl, &mut right_whdl);

            if had_space {
                drop(parent_whdl); // drop RefCell RefMut incase it was root
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

    // ------------ Delete -------------------------------------------------------------------------

    pub(crate) fn delete<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8],
    ) -> Result<(), PagerErr> {
        // TODO
        let traversal = self.traverse_cow(tx, key)?;

        let page_full_enough = {
            let (mut leaf, _) = traversal.last_mut();
            let (page_full_enough, page_empty) = {
                let mut curr_page = BtreePage::from_buffer(leaf.buf);
                curr_page.delete(key);
                (curr_page.is_half_full_or_more(), curr_page.len() == 0)
            };

            page_full_enough
        };

        if true || page_full_enough {
            // if we had space to insert we just are good
            self.root_pgid = traversal.index_ref(0).0.get_pgid();
            return Ok(());
        }

        todo!()
    }

    // ---------------------------------------------------------------------------------------------
    // *            Freelist Methods                                                               *
    // ---------------------------------------------------------------------------------------------

    // ------------ Pop min leq --------------------------------------------------------------------

    /// Removes and returns the minimum entry if its key is <= `bound`, otherwise returns `None`.
    /// TODO this is CoWing even if we dont make a change,
    pub(crate) fn pop_min_lt<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, bound: &[u8],
    ) -> Result<Option<SerializedU64>, PagerErr> {
        let mut traversal = Traversal::<WrHdl<'_>>::new();
        let mut next_pgid = self.root_pgid;

        loop {
            let whdl = tx.get_page_write(next_pgid)?;

            if traversal.len() > 0 {
                let (mut parent_whdl, slot_idx) = traversal.last_mut();
                let mut parent_page = BtreePage::from_buffer(parent_whdl.buf);
                parent_page.overwrite_value_with_slot_index(slot_idx, whdl.get_pgid().into());
            }

            let curr_page = BtreePage::from_buffer(whdl.buf);

            match curr_page.get_page_type() {
                BtreePageType::Inner => {
                    if curr_page.len() == 0 {
                        return Ok(None);
                    }
                    next_pgid = curr_page.entry_at_slot(0).1.get();
                    traversal.push((whdl, 0));
                }
                BtreePageType::Leaf => {
                    traversal.push((whdl, SLOT_IDX_NULL));
                    break;
                }
            }
        }

        let mut key = [0u8; BTREE_KEY_MAX_LEN];
        let (keylen, val) = {
            let (mut leaf, _) = traversal.last_mut();
            let curr_page = BtreePage::from_buffer(leaf.buf);
            if curr_page.len() == 0 {
                return Ok(None);
            }
            let (k, v) = curr_page.entry_at_slot(0);
            if k >= bound {
                return Ok(None);
            }
            key[..k.len()].copy_from_slice(k);
            (k.len(), v)
        };

        {
            let (mut leaf, _) = traversal.last_mut();
            let mut curr_page = BtreePage::from_buffer(leaf.buf);
            curr_page.delete(&key[..keylen]);
        }

        self.root_pgid = traversal.index_ref(0).0.get_pgid();
        Ok(Some(val))
    }
}

// -------------------------------------------------------------------------------------------------
// *            Cursor - TODO just rewrite this lul                                                *
// -------------------------------------------------------------------------------------------------

pub(crate) struct FreelistCursor<'tx> {
    stack: Traversal<RdHdl<'tx>>,
    leaf:  Option<(RdHdl<'tx>, u16)>,
}

impl<'tx> FreelistCursor<'tx> {
    pub(crate) fn new<R: PageReader<'tx>>(tx: &R, root_pgid: u64) -> Result<Self, PagerErr> {
        let mut cursor = Self { stack: Traversal::new(), leaf: None };
        cursor.descend_leftmost(tx, root_pgid)?;
        Ok(cursor)
    }

    fn descend_leftmost<R: PageReader<'tx>>(
        &mut self, tx: &R, mut pgid: u64,
    ) -> Result<(), PagerErr> {
        loop {
            let rhdl = tx.get_page_read(pgid)?;
            let (page_type, next_pgid_opt) = {
                let page = BtreePage::from_buffer_ref(rhdl.buf);
                let pt = page.get_page_type();
                let np = if matches!(pt, BtreePageType::Inner) && page.len() > 0 {
                    Some(page.entry_at_slot(0).1.get())
                } else {
                    None
                };
                (pt, np)
            };
            match page_type {
                BtreePageType::Inner => match next_pgid_opt {
                    Some(np) => {
                        pgid = np;
                        self.stack.push((rhdl, 0));
                    }
                    None => return Ok(()),
                },
                BtreePageType::Leaf => {
                    self.leaf = Some((rhdl, 0));
                    return Ok(());
                }
            }
        }
    }

    pub(crate) fn next<R: PageReader<'tx>>(
        &mut self, tx: &R,
    ) -> Result<Option<FreeEntry>, PagerErr> {
        loop {
            let maybe_val = match self.leaf {
                Some((ref rhdl, slot)) => {
                    // TODO HACK
                    let page = BtreePage::from_buffer_ref(rhdl.buf);
                    if slot < page.len() {
                        let key = page.entry_at_slot(slot).0;
                        let free_entry = FreeEntry::read_from_bytes(key);
                        Some(free_entry)
                    } else {
                        None
                    }
                }
                None => None,
            };

            if let Some(val) = maybe_val {
                self.leaf.as_mut().unwrap().1 += 1;
                return Ok(Some(val));
            }

            self.leaf = None;

            // Walk up the stack to find the next unvisited child, popping exhausted levels.
            let next_pgid = loop {
                if self.stack.len() == 0 {
                    return Ok(None);
                }
                let (next_slot, pgid_opt) = {
                    let (ref rhdl, slot) = self.stack.last_ref();
                    let page = BtreePage::from_buffer_ref(rhdl.buf);
                    let ns = slot + 1;
                    if ns < page.len() {
                        (ns, Some(page.entry_at_slot(ns).1.get()))
                    } else {
                        (ns, None)
                    }
                };
                if let Some(pgid) = pgid_opt {
                    *self.stack.last_slot_mut() = next_slot;
                    break pgid;
                } else {
                    self.stack.pop();
                }
            };

            self.descend_leftmost(tx, next_pgid)?;
        }
    }
}

// -------------------------------------------------------------------------------------------------
// *            Helpers                                                                            *
// -------------------------------------------------------------------------------------------------

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
