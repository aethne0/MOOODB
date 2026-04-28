// TODO we can optimze `get_index` and `len` by keeping an entry count on inner pages, which should
// be roughly free to maintain because of CoW
// TODO obviously for the freelist index thing we should just be keeping a cursor/iterator
//
// TODO key-only freelist btree
use super::page_btree::BtreePage;
use super::page_btree::BtreePageType;
use super::page_btree::SearchResult;
use super::serialization::*;
use super::storage_manager::*;
use super::PagerErr;
use crate::collections::StackArray;
use crate::mooo_assert;

const TRAVERSAL_LENGTH: usize = 64;
type Traversal<T> = StackArray<(T, u16), TRAVERSAL_LENGTH>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dir {
    Left,
    Right,
}

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
                let (parent_whdl, slot_index) = traversal.last_mut();
                let mut parent_page = BtreePage::from_buffer(parent_whdl.buf);
                parent_page.overwrite_value_at_slot_index(*slot_index, whdl.get_pgid().into());
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
        let mut traversal = self.traverse_cow(tx, key)?;
        self.root_pgid = traversal.first_ref().0.get_pgid();
        self.insert_inner(tx, &mut traversal, key, val)?;
        Ok(())
    }

    fn insert_inner<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, traversal: &mut Traversal<WrHdl<'tx>>, key: &[u8],
        val: SerializedU64,
    ) -> Result<(), PagerErr> {
        mooo_assert!(traversal.len() > 0);
        let at_root = traversal.len() == 1;

        let whdl_sibling_opt = insert_single_level(tx, traversal, key, val)?;
        let Some(mut whdl_sibling) = whdl_sibling_opt else {
            return Ok(());
        };

        let (mut whdl, _) = traversal.pop_unchecked();

        if at_root {
            let mut whdl_root = tx.get_page_alloc()?;
            BtreePage::new_with_buffer(whdl_root.buf, BtreePageType::Inner);
            insert_child_ptr(&mut whdl_root, &mut whdl);
            insert_child_ptr(&mut whdl_root, &mut whdl_sibling);
            self.root_pgid = whdl_root.get_pgid();
            return Ok(());
        }

        // at this point:
        // - we have overflowed and spilled into a new right sibling
        // - we are not the root
        // also, the top of `traversal` is currently our parent

        // Were going to re-insert both these children
        let (whdl_parent, slot) = traversal.last_mut();
        let mut page_parent = BtreePage::from_buffer(whdl_parent.buf);
        page_parent.delete_slot_entry(*slot);

        let pgid = whdl.get_pgid();
        let page = BtreePage::from_buffer_ref(whdl.buf);
        let key = page.entry_at_slot(0).0;
        self.insert_inner(tx, traversal, key, pgid.into())?;

        let pgid_sibling = whdl_sibling.get_pgid();
        let page_sibling = BtreePage::from_buffer_ref(whdl_sibling.buf);
        let key = page_sibling.entry_at_slot(0).0;
        self.insert_inner(tx, traversal, key, pgid_sibling.into())?;

        Ok(())
    }

    // ------------ Delete -------------------------------------------------------------------------

    pub(crate) fn delete<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8],
    ) -> Result<bool, PagerErr> {
        let mut traversal = self.traverse_cow(tx, key)?;
        self.root_pgid = traversal.first_ref().0.get_pgid();

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
                    slotidx_opt = self.delete_single_level(tx, &mut traversal, slotidx)?;
                }
            }
        }
    }

    /// Pops topmost entry from traversal stack
    /// returns true we deleted a leaf page
    /// TODO doc
    fn delete_single_level<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, traversal: &mut Traversal<WrHdl<'tx>>, slot_index: u16,
    ) -> Result<Option<u16>, PagerErr> {
        mooo_assert!(traversal.len() > 0);
        let (mut whdl, _) = traversal.pop_unchecked();
        let pgid = whdl.get_pgid();
        let mut page = BtreePage::from_buffer(whdl.buf);
        let is_root = traversal.len() == 0;
        mooo_assert!(page.len() > 0);

        // remove from the leaf
        page.delete_slot_entry(slot_index);

        if page.is_full_enough() {
            return Ok(None);
        }

        if is_root && page.is_leaf() {
            return Ok(None);
        }

        if is_root && page.is_inner() {
            mooo_assert!(page.len() > 0);
            if page.len() == 1 {
                // assign root to our only child, and free self
                self.root_pgid = page.entry_at_slot(0).1.get();
                drop(whdl);
                tx.free_page(pgid)?;
            }
            return Ok(None);
        }

        let (whdl_parent, slotidx_parent_to_leaf_) = traversal.last_mut();
        let slotidx_parent_to_leaf = *slotidx_parent_to_leaf_;
        let page_parent = BtreePage::from_buffer(whdl_parent.buf);

        // By this point, our node is:
        // - not the root
        mooo_assert!(!is_root);
        // - underflowing
        mooo_assert!(!page.is_full_enough());
        // - has at least one sibling
        mooo_assert!(page_parent.len() > 1);

        let has_sibling_to_left = slotidx_parent_to_leaf > 0;
        let has_sibling_to_right = slotidx_parent_to_leaf < page_parent.len() - 1;

        // first well see if we can merge, this is ideal
        if has_sibling_to_left {
            let slot_opt = try_merge_with_sibling(
                tx,
                &mut whdl,
                whdl_parent,
                Dir::Left,
                slotidx_parent_to_leaf,
            )?;
            if slot_opt.is_some() {
                return Ok(slot_opt);
            }
        }

        if has_sibling_to_right {
            let slot_opt = try_merge_with_sibling(
                tx,
                &mut whdl,
                whdl_parent,
                Dir::Right,
                slotidx_parent_to_leaf,
            )?;
            if slot_opt.is_some() {
                return Ok(slot_opt);
            }
        }

        // otherwise try to borrow
        if has_sibling_to_left {
            let slot_opt = try_borrow_from_sibling(
                tx,
                &mut whdl,
                whdl_parent,
                Dir::Left,
                slotidx_parent_to_leaf,
            )?;

            if slot_opt.is_some() {
                return Ok(slot_opt);
            }
        }

        if has_sibling_to_right {
            let slot_opt = try_borrow_from_sibling(
                tx,
                &mut whdl,
                whdl_parent,
                Dir::Right,
                slotidx_parent_to_leaf,
            )?;

            if slot_opt.is_some() {
                return Ok(slot_opt);
            }
        }

        // This is possible in cases where we are at 49% capacity and our sibling is >50% but taking a
        // single key would bring it under 50%.
        // Borrowing would not work (sibling now <50%) but neither would merging (>100%).
        Ok(None)
    }
}

// -------------------------------------------------------------------------------------------------
//                                                                    ▪   ▐ ▄ .▄▄ · ▄▄▄ .▄▄▄  ▄▄▄▄▄
//                                                                    ██ •█▌▐█▐█ ▀. ▀▄.▀·▀▄ █·•██
//                                                                    ▐█·▐█▐▐▌▄▀▀▀█▄▐▀▀▪▄▐▀▀▄  ▐█.▪
//  Insertion                                                         ▐█▌██▐█▌▐█▄▪▐█▐█▄▄▌▐█•█▌ ▐█▌·
//                                                                    ▀▀▀▀▀ █▪ ▀▀▀▀  ▀▀▀ .▀  ▀ ▀▀▀
// -------------------------------------------------------------------------------------------------

/// Traversal stack will stay the same
/// May return new right child, if split occured
fn insert_single_level<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
    tx: &mut R, traversal: &mut Traversal<WrHdl<'tx>>, key: &[u8], val: SerializedU64,
) -> Result<Option<WrHdl<'tx>>, PagerErr> {
    let (whdl, _) = traversal.last_mut();

    let had_space = {
        let mut page = BtreePage::from_buffer(whdl.buf);
        page.insert(key, val)
    };
    if had_space {
        return Ok(None);
    }

    let (mut whdl, slot) = traversal.pop_unchecked();
    // let (parent_whdl, parent_slot) = traversal.last_mut();

    let mut whdl_sibling = tx.get_page_alloc()?;
    redistribute_into_uninit_right(&mut whdl, &mut whdl_sibling, key, val);

    traversal.push((whdl, slot));
    Ok(Some(whdl_sibling))
}

/// Inserts a pointer in parent pointing to child, using the child whdl pgid and leftmost key.
/// These pages should be initialized.
/// **Return**'s whether or not insert had space - nothing was done if there was no space
fn insert_child_ptr(whdl_parent: &mut WrHdl<'_>, whdl_child: &mut WrHdl<'_>) -> bool {
    // insert split leafs into new root
    let pgid_child = whdl_child.get_pgid();
    let page_child = BtreePage::from_buffer(whdl_child.buf);
    let mut page_parent = BtreePage::from_buffer(whdl_parent.buf);
    page_parent.insert(page_child.entry_at_slot(0).0, pgid_child.into())
}

/// left should be initialized, right should NOT be initiliazed
fn redistribute_into_uninit_right(
    whdl_left: &mut WrHdl<'_>, whdl_right: &mut WrHdl<'_>, key: &[u8], val: SerializedU64,
) {
    let mut left = BtreePage::from_buffer(whdl_left.buf);
    let mut right = BtreePage::new_with_buffer(whdl_right.buf, left.get_page_type());
    left.redistribute_into(&mut right);
    if key < right.entry_at_slot(0).0 {
        let _had_space = left.insert(key, val);
        mooo_assert!(_had_space);
    } else {
        let _had_space = right.insert(key, val);
        mooo_assert!(_had_space);
    }
}

// -------------------------------------------------------------------------------------------------
//                                                                 ·▄▄▄▄  ▄▄▄ .▄▄▌  ▄▄▄ .▄▄▄▄▄▄▄▄ .
//                                                                 ██▪ ██ ▀▄.▀·██•  ▀▄.▀·•██  ▀▄.▀·
//                                                                 ▐█· ▐█▌▐▀▀▪▄██▪  ▐▀▀▪▄ ▐█.▪▐▀▀▪▄
//  Deletion                                                       ██. ██ ▐█▄▄▌▐█▌▐▌▐█▄▄▌ ▐█▌·▐█▄▄▌
//                                                                 ▀▀▀▀▀•  ▀▀▀ .▀▀▀  ▀▀▀  ▀▀▀  ▀▀▀
// -------------------------------------------------------------------------------------------------

fn try_merge_with_sibling<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
    tx: &mut R, whdl: &mut WrHdl<'tx>, whdl_parent: &mut WrHdl<'tx>, dir_to_sibling: Dir,
    slotidx_parent_to_leaf: u16,
) -> Result<Option<u16>, PagerErr> {
    let mut page_parent = BtreePage::from_buffer(whdl_parent.buf);

    let pgid = whdl.get_pgid();
    let page = BtreePage::from_buffer(whdl.buf);

    let slotidx_parent_to_sibling = match dir_to_sibling {
        Dir::Left => slotidx_parent_to_leaf - 1,
        Dir::Right => slotidx_parent_to_leaf + 1,
    };
    let pgid_sibling = page_parent.entry_at_slot(slotidx_parent_to_sibling).1.get();
    let rhdl_sibling = tx.get_page_read(pgid_sibling)?;

    let can_merge = {
        let rhdl_sib = tx.get_page_read(pgid_sibling)?;
        let page_sib = BtreePage::from_buffer_ref(rhdl_sib.buf);
        page.could_merge_with(&page_sib)
    };
    if !can_merge {
        return Ok(None);
    };

    absorb_and_free_sibling(tx, whdl, rhdl_sibling, dir_to_sibling)?;

    // have to make sure we are deleting whichever slot had the higher key - we set both slots to
    // our pgid and delete the higher-keyed one
    page_parent.overwrite_value_at_slot_index(slotidx_parent_to_sibling, pgid.into());
    let to_delete = match dir_to_sibling {
        Dir::Left => slotidx_parent_to_leaf,
        Dir::Right => slotidx_parent_to_sibling,
    };
    Ok(Some(to_delete))
}

fn try_borrow_from_sibling<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
    tx: &mut R, whdl: &mut WrHdl<'tx>, whdl_parent: &mut WrHdl<'tx>, dir_to_sibling: Dir,
    slotidx_parent_to_leaf: u16,
) -> Result<Option<u16>, PagerErr> {
    let mut page_parent = BtreePage::from_buffer(whdl_parent.buf);

    let slotidx_parent_to_sibling = match dir_to_sibling {
        Dir::Left => slotidx_parent_to_leaf - 1,
        Dir::Right => slotidx_parent_to_leaf + 1,
    };
    let pgid_sibling_old = page_parent.entry_at_slot(slotidx_parent_to_sibling).1.get();
    let can_borrow = {
        let rhdl_sib = tx.get_page_read(pgid_sibling_old)?;
        let page_sib = BtreePage::from_buffer_ref(rhdl_sib.buf);
        page_sib.is_full_enough_without_last()
    };
    if !can_borrow {
        return Ok(None);
    };

    let whdl_sibling = tx.get_page_write(pgid_sibling_old)?;

    let pgid = whdl.get_pgid();

    let mut page = BtreePage::from_buffer(whdl.buf);
    let mut page_sibling = BtreePage::from_buffer(whdl_sibling.buf);

    let donor_slot = match dir_to_sibling {
        Dir::Left => page_sibling.len() - 1,
        Dir::Right => 0,
    };
    let (key, val) = page_sibling.entry_at_slot(donor_slot);
    page.insert(key, val);
    page_sibling.delete_slot_entry(donor_slot);

    // we do this to update our entry in the parent, because we may have a new lowest key
    page_parent.delete_slot_entry(slotidx_parent_to_leaf);
    page_parent.insert(page.entry_at_slot(0).0, pgid.into());

    Ok(Some(slotidx_parent_to_sibling))
}

/// Merges donor into receiver - doesn't mutate donor
///
/// If `donor` is RIGHT of the `receiver` then `direction_to_donor` should be `SiblingDir::Right`
fn absorb_and_free_sibling<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
    tx: &mut R, receiver: &mut WrHdl<'_>, donor: RdHdl<'_>, dir_to_donor: Dir,
) -> Result<(), PagerErr> {
    let mut page_receiver = BtreePage::from_buffer(receiver.buf);
    let page_donor = BtreePage::from_buffer_ref(donor.buf);

    match dir_to_donor {
        Dir::Left => {
            // donor is to our left, so keys will be less than ours, so we can't just append them
            for (key, val) in &page_donor {
                page_receiver.insert(key, val);
            }
        }
        Dir::Right => {
            for (key, val) in &page_donor {
                page_receiver.insert_unordered(key, val);
            }
        }
    }

    let pgid = donor.get_pgid();
    drop(donor);
    tx.free_page(pgid)?;
    Ok(())
}
