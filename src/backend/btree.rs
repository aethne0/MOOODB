// TODO btree delete rebalancing
//
// TODO we can optimze `get_index` and `len` by keeping an entry count on inner pages, which should
// be roughly free to maintain because of CoW
// TODO obviously for the freelist index thing we should just be keeping a cursor/iterator
//
// TODO key-only freelist btree
//
// TODO In delete there are some sorted inserts that could be optimized

use std::cell::Ref;
use std::cell::RefCell;
use std::cell::RefMut;
use std::mem::MaybeUninit;

use super::page_btree::BtreePage;
use super::page_btree::BtreePageType;
use super::page_btree::SearchResult;
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
                parent_page.overwrite_value_at_slot_index(slot_index, whdl.get_pgid().into());
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

    // ------------ Delete -------------------------------------------------------------------------

    pub(crate) fn delete<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8],
    ) -> Result<bool, PagerErr> {
        let mut traversal = self.traverse_cow(tx, key)?;

        let mut slotidx_opt = Some({
            let (whdl_leaf, _) = traversal.last_ref();
            let page_leaf = BtreePage::from_buffer_ref(whdl_leaf.buf);
            let SearchResult::Found(slotidx) = page_leaf.find_slot_from_key(key) else {
                return Ok(false);
            };
            slotidx
        });

        loop {
            match slotidx_opt {
                None => return Ok(true),
                Some(slotidx) => {
                    slotidx_opt = self.delete_and_pop(tx, &mut traversal, slotidx)?;
                }
            }
        }
    }

    /// returns true we deleted a leaf page
    /// TODO doc
    /// Pops topmost entry from traversal
    fn delete_and_pop<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, traversal: &mut Traversal<WrHdl<'_>>, slot_index: u16,
    ) -> Result<Option<u16>, PagerErr> {
        mooo_assert!(traversal.len() > 0);
        self.root_pgid = traversal.index_ref(0).0.get_pgid();

        // remove from leaf
        let (mut whdl, _) = traversal.pop();
        let pgid = whdl.get_pgid();
        let mut page = BtreePage::from_buffer(whdl.buf);
        let is_root = self.root_pgid == pgid;
        mooo_assert!(page.len() > 0);
        page.delete_slot_entry(slot_index);

        // if `is_root` we return in these branches

        if is_root && page.is_leaf() {
            // we are the root, and a leaf node, were good even if were empty
            return Ok(None);
        }

        if is_root && page.is_inner() {
            mooo_assert!(page.len() > 0);
            // we are the root, and an inner node

            if page.len() > 1 {
                // if we have >1 child we are good
                return Ok(None);
            }

            // if we only have 1 child we will just suck them
            // Don't forget that if we suck a singular leaf child we should become a leaf ourself

            let pgid_child = {
                let pgid_child = page.entry_at_slot(0).1.get();
                let rhdl_child = tx.get_page_read(pgid_child)?;
                let page_child = BtreePage::from_buffer_ref(rhdl_child.buf);

                page.clear();
                page.set_page_type(page_child.get_page_type());
                for (key, val) in &page_child {
                    page.insert(key, val);
                }
                pgid_child
            };

            tx.free_page(pgid_child)?;
            return Ok(None);
        }

        if page.is_full_enough() {
            // this page is not underflowing -> were good
            return Ok(None);
        }

        let (whdl_parent, parent_slotidx_to_leaf) = traversal.pop();
        let mut page_parent = BtreePage::from_buffer(whdl_parent.buf);

        // By this point, our node is:
        // - not the root
        mooo_assert!(!is_root);
        // - underflowing
        mooo_assert!(!page.is_full_enough());
        // - has at least one sibling
        mooo_assert!(page_parent.len() > 1);

        // we will try to borrow from left sibling (if exists),
        // then try to borrow from right sibling (if exists)

        // TODO we can probably deduplicate this right/left logic
        if parent_slotidx_to_leaf > 0 {
            // theres a sibling to our left
            let pgid_sibling_old = page_parent.entry_at_slot(parent_slotidx_to_leaf - 1).1.get();
            let can_borrow = {
                let rhdl_sibling = tx.get_page_read(pgid_sibling_old)?;
                let page_sibling = BtreePage::from_buffer_ref(rhdl_sibling.buf);
                page_sibling.is_full_enough_without_last()
            };

            if can_borrow {
                // this sibling is full enough to borrow from
                let whdl_sibling = tx.get_page_write(pgid_sibling_old)?;
                let pgid_sibling = whdl_sibling.get_pgid();
                let mut page_sibling = BtreePage::from_buffer(whdl_sibling.buf);
                let (key, val) = page_sibling.entry_at_slot(page_sibling.len() - 1);
                page.insert(key, val);
                page_sibling.delete_slot_entry(page_sibling.len() - 1);
                mooo_assert!(page_sibling.len() > 0);
                mooo_assert!(page_sibling.is_full_enough());
                mooo_assert!(page.is_full_enough());

                // we have a new leftmost key -> we need to update our parents pointer to us
                page_parent.delete_slot_entry(parent_slotidx_to_leaf);
                page_parent.insert(page.entry_at_slot(0).0, pgid.into());
                // then also update our siblings newly CoW'd pointer
                page_parent.delete_slot_entry(parent_slotidx_to_leaf - 1);
                page_parent.insert(page_sibling.entry_at_slot(0).0, pgid_sibling.into());
                return Ok(None);
            }
        }

        if parent_slotidx_to_leaf < page_parent.len() - 1 {
            // theres a sibling to our right
            let pgid_sibling_old = page_parent.entry_at_slot(parent_slotidx_to_leaf + 1).1.get();
            let can_borrow = {
                let rhdl_sibling = tx.get_page_read(pgid_sibling_old)?;
                let page_sibling = BtreePage::from_buffer_ref(rhdl_sibling.buf);
                page_sibling.is_full_enough_without_first()
            };

            if can_borrow {
                // this sibling is full enough to borrow from
                let whdl_sibling = tx.get_page_write(pgid_sibling_old)?;
                let pgid_sibling = whdl_sibling.get_pgid();
                let mut page_sibling = BtreePage::from_buffer(whdl_sibling.buf);
                let (key, val) = page_sibling.entry_at_slot(0);
                page.insert(key, val);
                page_sibling.delete_slot_entry(0);
                mooo_assert!(page_sibling.len() > 0);
                mooo_assert!(page_sibling.is_full_enough());
                mooo_assert!(page.is_full_enough());

                // right sibling has a new leftmost key -> we need to update the parent's
                // pointer to it
                page_parent.delete_slot_entry(parent_slotidx_to_leaf + 1);
                page_parent.insert(page_sibling.entry_at_slot(0).0, pgid_sibling.into());
                return Ok(None);
            }
        }

        // note: we are only holding whdl_leaf and whdl_parent right now
        //       We also haven't CoW'd a sibling yet

        // we couldn't borrow from a sibling, so we need to merge
        // well take left sibling if exists, otherwise right
        let (dir_sibling, parent_slotidx_to_sibling) = if parent_slotidx_to_leaf > 0 {
            (SiblingDir::Left, parent_slotidx_to_leaf - 1)
        } else {
            (SiblingDir::Right, parent_slotidx_to_leaf + 1)
        };

        let pgid_sibling = page_parent.entry_at_slot(parent_slotidx_to_sibling).1.get();
        let rhdl_sibling = tx.get_page_read(pgid_sibling)?;

        let page_leaf = {
            drop(page);
            merge(&mut whdl, &rhdl_sibling, dir_sibling);
            BtreePage::from_buffer(whdl.buf)
        };

        if dir_sibling == SiblingDir::Left {
            // if sibling was on our left, then our lowest key changed, so we need to update ptr
            // idx-1 because our slot index was decrementing from deleting our left sibling!
            page_parent.delete_slot_entry(parent_slotidx_to_leaf - 1);
            page_parent.insert(page_leaf.entry_at_slot(0).0, pgid.into());
        }

        mooo_assert!(page_leaf.is_full_enough());
        traversal.push((whdl_parent, SLOT_INDEX_NULL));
        tx.free_page(pgid_sibling)?;
        Ok(Some(parent_slotidx_to_sibling))
    }
}

// ------------ Helpers ----------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum SiblingDir {
    Left,
    Right,
}

/// Inserts a pointer in parent pointing to child, using the child whdl pgid and leftmost key.
/// These pages should be initialized.
/// **Return**'s whether or not insert had space - nothing was done if there was no space
fn insert_child_ptr(parent_whdl: &mut WrHdl<'_>, child_whdl: &mut WrHdl<'_>) -> bool {
    // insert split leafs into new root
    let child_pgid = child_whdl.get_pgid();
    let child_page = BtreePage::from_buffer(child_whdl.buf);
    let mut parent_page = BtreePage::from_buffer(parent_whdl.buf);
    parent_page.insert(child_page.entry_at_slot(0).0, child_pgid.into())
}

/// Merges donor into receiver - doesn't mutate donor
///
/// If `donor` is RIGHT of the `receiver` then `direction_to_donor` should be `SiblingDir::Right`
fn merge(receiver: &mut WrHdl<'_>, donor: &RdHdl<'_>, direction_to_donor: SiblingDir) {
    let mut receiver = BtreePage::from_buffer(receiver.buf);
    let donor = BtreePage::from_buffer_ref(donor.buf);

    match direction_to_donor {
        SiblingDir::Left => {
            // donor is to our left, so keys will be less than ours, so we can't just append them
            for (key, val) in &donor {
                receiver.insert(key, val);
            }
        }
        SiblingDir::Right => {
            for (key, val) in &donor {
                receiver.insert_unordered(key, val);
            }
        }
    }

    #[cfg(debug_assertions)]
    receiver.compact();
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
const STACK_SIZE: usize = 64;
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
