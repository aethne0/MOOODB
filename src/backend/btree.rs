use std::ops::AddAssign;

use super::page_btree::*;
use super::serialization::*;
use super::storage_manager::*;
use super::PagerErr;
use crate::backend::PGID_NULL;
use crate::collections::FixedArray;
use crate::mooo_assert;
use crate::util::fmt_bytes;

const TRAVERSAL_LENGTH: usize = 48;
type Traversal<T> = FixedArray<(T, u16), TRAVERSAL_LENGTH>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dir {
    Left,
    Right,
}

/// It is the responsibility of the caller to update anything that points to `root_pgid`
#[derive(Clone, Copy)]
pub(super) struct Btree {
    root_pgid: u64,
}

fn pgid_from_bytes(val: &[u8]) -> u64 {
    mooo_assert!(val.len() == size_of::<SerializedU64>());
    SerializedU64::read_from_bytes(val).get()
}

/// Handles endianness etc
fn bytes_from_pgid(pgid: u64) -> [u8; 8] {
    SerializedU64::from(pgid).0
}

impl Btree {
    /// Allocates and initializes btree root page
    #[must_use]
    pub(super) fn new<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        tx: &mut R,
    ) -> Result<Btree, PagerErr> {
        let whdl = tx.get_page_alloc()?;
        let pgid = whdl.get_pgid();
        BtreePage::new_with_buffer(whdl.buf, BtreePageType::Leaf);
        Ok(Self::from_pgid(pgid))
    }

    /// For opening an EXISTING btree
    #[must_use]
    pub(super) fn from_pgid(root_pgid: u64) -> Self {
        Self { root_pgid }
    }

    pub(super) fn get_root_pgid(&self) -> u64 {
        self.root_pgid
    }

    // ------------ Util ---------------------------------------------------------------------------

    fn traverse<'tx, R: PageReader<'tx>>(
        &self, tx: &R, key: &[u8],
    ) -> Result<Traversal<RdHdl<'tx>>, PagerErr> {
        let mut traversal = Traversal::<RdHdl<'_>>::new();
        let mut next_pgid = self.root_pgid;

        loop {
            let rhdl = tx.get_page_read(next_pgid)?;

            let curr_page = BtreePage::from_buffer_ref(rhdl.buf);

            match curr_page.get_page_type() {
                BtreePageType::Inner => {
                    let (pgid_entry, slot) = curr_page.get_traversal_next_page(key).unwrap();
                    next_pgid = pgid_from_bytes(pgid_entry);
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
                parent_page
                    .overwrite_value_at_slot_index(*slot_index, &bytes_from_pgid(whdl.get_pgid()));
            }

            let curr_page = BtreePage::from_buffer(whdl.buf);

            match curr_page.get_page_type() {
                BtreePageType::Inner => {
                    let (pgid_entry, slot) = curr_page.get_traversal_next_page(key).unwrap();
                    next_pgid = pgid_from_bytes(pgid_entry);
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

    /// Counts total number of entries in entire tree - recursive.
    pub(super) fn len<'tx, R: PageReader<'tx>>(&self, tx: &R) -> Result<usize, PagerErr> {
        let pgid = self.root_pgid;
        let mut count = 0;

        let page = BtreePage::from_buffer_ref(tx.get_page_read(pgid)?.buf);
        if page.is_leaf() {
            return Ok(page.len() as usize);
        }

        for slot_index in 0..page.len() {
            let child_pgid = pgid_from_bytes(page.key_val_slices_from_slot(slot_index).1);
            count += Btree::from_pgid(child_pgid).len(tx)?;
        }

        Ok(count)
    }

    /// Counts total number of entries in entire tree - recursive.
    /// (entry_count, leaf_page_count, inner_page_count, bytes_entries)
    pub(super) fn meta<'tx, R: PageReader<'tx>>(&self, tx: &R) -> Result<BtreeMeta, PagerErr> {
        let pgid = self.root_pgid;

        let page = BtreePage::from_buffer_ref(tx.get_page_read(pgid)?.buf);
        if page.is_leaf() {
            let meta = BtreeMeta {
                page_cnt_total: 1,
                page_cnt_leaf:  1,
                page_cnt_inner: 0,
                entry_cnt:      page.len() as u64,
                bytes:          page.entry_bytes() as u64,
            };
            return Ok(meta);
        }

        let mut meta = BtreeMeta {
            page_cnt_total: 1,
            page_cnt_leaf:  0,
            page_cnt_inner: 1,
            entry_cnt:      0,
            bytes:          0,
        };

        for slot_index in 0..page.len() {
            let pgid_child = pgid_from_bytes(page.key_val_slices_from_slot(slot_index).1);
            meta += Btree::from_pgid(pgid_child).meta(tx)?;
        }

        Ok(meta)
    }

    pub(super) fn cursor(&self) -> Cursor {
        Cursor::new(self.root_pgid)
    }

    // ---------------------------------------------------------------------------------------------
    //                                                                              ▄▄ • ▄▄▄ .▄▄▄▄▄
    //                                                                             ▐█ ▀ ▪▀▄.▀·•██
    //                                                                             ▄█ ▀█▄▐▀▀▪▄ ▐█.▪
    //  Get                                                                        ▐█▄▪▐█▐█▄▄▌ ▐█▌·
    //                                                                             ·▀▀▀▀  ▀▀▀  ▀▀▀
    // ---------------------------------------------------------------------------------------------

    /*
    pub(super) fn get<'tx, R: PageReader<'tx>>(
        &self, tx: &R, key: &[u8],
    ) -> Result<Option<&[u8]>, PagerErr> {
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

    pub(super) fn min<'tx, R: PageReader<'tx>>(
        &self, tx: &R,
    ) -> Result<Option<(&[u8], &[u8])>, PagerErr> {
        let mut next_pgid = self.root_pgid;

        loop {
            let page = BtreePage::from_buffer_ref(tx.get_page_read(next_pgid)?.buf);
            if page.len() == 0 {
                return Ok(None);
            }
            if page.is_leaf() {
                return Ok(Some(page.key_val_slices_from_slot(0).1));
            }
            next_pgid = page.key_val_slices_from_slot(0).1.get()
        }
    }

    pub(super) fn max<'tx, R: PageReader<'tx>>(
        &self, tx: &R,
    ) -> Result<Option<(&[u8], &[u8])>, PagerErr> {
        let mut next_pgid = self.root_pgid;

        loop {
            let page = BtreePage::from_buffer_ref(tx.get_page_read(next_pgid)?.buf);
            if page.len() == 0 {
                return Ok(None);
            }
            if page.is_leaf() {
                return Ok(Some(page.key_val_slices_from_slot(page.len() - 1).1));
            }
            next_pgid = page.key_val_slices_from_slot(page.len() - 1).1.get()
        }
    }
    */

    // ---------------------------------------------------------------------------------------------
    //                                                                ▪   ▐ ▄ .▄▄ · ▄▄▄ .▄▄▄  ▄▄▄▄▄
    //                                                                ██ •█▌▐█▐█ ▀. ▀▄.▀·▀▄ █·•██
    //                                                                ▐█·▐█▐▐▌▄▀▀▀█▄▐▀▀▪▄▐▀▀▄  ▐█.▪
    //  Insertion                                                     ▐█▌██▐█▌▐█▄▪▐█▐█▄▄▌▐█•█▌ ▐█▌·
    //                                                                ▀▀▀▀▀ █▪ ▀▀▀▀  ▀▀▀ .▀  ▀ ▀▀▀
    // ---------------------------------------------------------------------------------------------

    pub(super) fn insert<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, key: &[u8], val: &[u8],
    ) -> Result<(), PagerErr> {
        let mut traversal = self.traverse_cow(tx, key)?;
        self.root_pgid = traversal.first_ref().0.get_pgid();
        self.insert_inner(tx, &mut traversal, key, val)?;
        Ok(())
    }

    fn insert_inner<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        &mut self, tx: &mut R, traversal: &mut Traversal<WrHdl<'tx>>, key: &[u8], val: &[u8],
    ) -> Result<(), PagerErr> {
        mooo_assert!(traversal.len() > 0);
        let at_root = traversal.len() == 1;

        let whdl_sibling_opt = Self::insert_single_level(tx, traversal, key, val)?;
        let Some(mut whdl_sibling) = whdl_sibling_opt else {
            return Ok(());
        };

        let (mut whdl, _) = traversal.pop_unchecked();

        if at_root {
            let mut whdl_root = tx.get_page_alloc()?;
            BtreePage::new_with_buffer(whdl_root.buf, BtreePageType::Inner);
            Self::insert_child_ptr(&mut whdl_root, &mut whdl);
            Self::insert_child_ptr(&mut whdl_root, &mut whdl_sibling);
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
        let key = page.key_val_slices_from_slot(0).0;
        self.insert_inner(tx, traversal, key, &bytes_from_pgid(pgid))?;

        let pgid_sibling = whdl_sibling.get_pgid();
        let page_sibling = BtreePage::from_buffer_ref(whdl_sibling.buf);
        let key = page_sibling.key_val_slices_from_slot(0).0;
        self.insert_inner(tx, traversal, key, &bytes_from_pgid(pgid_sibling))?;

        Ok(())
    }

    /// Traversal stack will stay the same
    /// May return new right child, if split occured
    fn insert_single_level<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        tx: &mut R, traversal: &mut Traversal<WrHdl<'tx>>, key: &[u8], val: &[u8],
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
        Self::redistribute_into_uninit_right(&mut whdl, &mut whdl_sibling, key, val);

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
        page_parent.insert(page_child.key_val_slices_from_slot(0).0, &bytes_from_pgid(pgid_child))
    }

    /// left should be initialized, right should NOT be initiliazed
    fn redistribute_into_uninit_right(
        whdl_left: &mut WrHdl<'_>, whdl_right: &mut WrHdl<'_>, key: &[u8], val: &[u8],
    ) {
        let mut left = BtreePage::from_buffer(whdl_left.buf);
        let mut right = BtreePage::new_with_buffer(whdl_right.buf, left.get_page_type());
        left.redistribute_into(&mut right);
        if key < right.key_val_slices_from_slot(0).0 {
            let _had_space = left.insert(key, val);
            mooo_assert!(_had_space);
        } else {
            let _had_space = right.insert(key, val);
            mooo_assert!(_had_space);
        }
    }

    // ---------------------------------------------------------------------------------------------
    //                                                             ·▄▄▄▄  ▄▄▄ .▄▄▌  ▄▄▄ .▄▄▄▄▄▄▄▄ .
    //                                                             ██▪ ██ ▀▄.▀·██•  ▀▄.▀·•██  ▀▄.▀·
    //                                                             ▐█· ▐█▌▐▀▀▪▄██▪  ▐▀▀▪▄ ▐█.▪▐▀▀▪▄
    //  Deletion                                                   ██. ██ ▐█▄▄▌▐█▌▐▌▐█▄▄▌ ▐█▌·▐█▄▄▌
    //                                                             ▀▀▀▀▀•  ▀▀▀ .▀▀▀  ▀▀▀  ▀▀▀  ▀▀▀
    // ---------------------------------------------------------------------------------------------

    pub(super) fn delete<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
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
                self.root_pgid = pgid_from_bytes(page.key_val_slices_from_slot(0).1);
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
            let slot_opt = Self::try_merge_with_sibling(
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
            let slot_opt = Self::try_merge_with_sibling(
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
            let slot_opt = Self::try_borrow_from_sibling(
                tx,
                &mut whdl,
                whdl_parent,
                Dir::Left,
                slotidx_parent_to_leaf,
            )?;

            if slot_opt.is_some() {
                return Ok(None);
            }
        }

        if has_sibling_to_right {
            let slot_opt = Self::try_borrow_from_sibling(
                tx,
                &mut whdl,
                whdl_parent,
                Dir::Right,
                slotidx_parent_to_leaf,
            )?;

            if slot_opt.is_some() {
                return Ok(None);
            }
        }

        // This is possible in cases where we are at 49% capacity and our sibling is >50% but taking
        // a single key would bring it under 50%.
        // Borrowing would not work (sibling now <50%) but neither would merging (>100%).
        Ok(None)
    }

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
        let pgid_sibling =
            pgid_from_bytes(page_parent.key_val_slices_from_slot(slotidx_parent_to_sibling).1);
        let rhdl_sibling = tx.get_page_read(pgid_sibling)?;

        let can_merge = {
            let rhdl_sib = tx.get_page_read(pgid_sibling)?;
            let page_sib = BtreePage::from_buffer_ref(rhdl_sib.buf);
            page.could_merge_with(&page_sib)
        };
        if !can_merge {
            return Ok(None);
        };

        Self::absorb_and_free_sibling(tx, whdl, rhdl_sibling, dir_to_sibling)?;

        // have to make sure we are deleting whichever slot had the higher key - we set both slots
        // to our pgid and delete the higher-keyed one
        page_parent
            .overwrite_value_at_slot_index(slotidx_parent_to_sibling, &bytes_from_pgid(pgid));
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
        let pgid_sibling_old =
            pgid_from_bytes(page_parent.key_val_slices_from_slot(slotidx_parent_to_sibling).1);
        let can_borrow = {
            let rhdl_sib = tx.get_page_read(pgid_sibling_old)?;
            let page_sib = BtreePage::from_buffer_ref(rhdl_sib.buf);
            page_sib.is_full_enough_without_last()
        };
        if !can_borrow {
            return Ok(None);
        };

        let whdl_sibling = tx.get_page_write(pgid_sibling_old)?;
        let pgid_sibling = whdl_sibling.get_pgid();

        let pgid = whdl.get_pgid();

        let mut page = BtreePage::from_buffer(whdl.buf);
        let mut page_sibling = BtreePage::from_buffer(whdl_sibling.buf);

        let donor_slot = match dir_to_sibling {
            Dir::Left => page_sibling.len() - 1,
            Dir::Right => 0,
        };
        let (key, val) = page_sibling.key_val_slices_from_slot(donor_slot);
        page.insert(key, val);
        page_sibling.delete_slot_entry(donor_slot);

        {
            // TODO improve
            // we do this to update our entry in the parent, because we may have a new lowest key
            match dir_to_sibling {
                Dir::Left => {
                    // if sibling is on our left, our new lowest key changes to its old highest key
                    page_parent.delete_slot_entry(slotidx_parent_to_leaf);
                    page_parent.delete_slot_entry(slotidx_parent_to_sibling);
                }
                Dir::Right => {
                    // if it was on the right then vice-versa
                    page_parent.delete_slot_entry(slotidx_parent_to_sibling);
                    page_parent.delete_slot_entry(slotidx_parent_to_leaf);
                }
            }

            page_parent.insert(page.key_val_slices_from_slot(0).0, &bytes_from_pgid(pgid));
            page_parent
                .insert(page_sibling.key_val_slices_from_slot(0).0, &bytes_from_pgid(pgid_sibling));
        }

        Ok(Some(slotidx_parent_to_sibling))
    }

    /// Merges donor into receiver - doesn't mutate donor
    ///
    /// If `donor` is RIGHT of `receiver` then `direction_to_donor` should be `SiblingDir::Right`
    /// ASSUMES PAGES ARE INITIALIZED
    fn absorb_and_free_sibling<'tx, R: PageReader<'tx> + PageWriter<'tx>>(
        tx: &mut R, receiver: &mut WrHdl<'_>, donor: RdHdl<'_>, dir_to_donor: Dir,
    ) -> Result<(), PagerErr> {
        let mut page_receiver = BtreePage::from_buffer(receiver.buf);
        let page_donor = BtreePage::from_buffer_ref(donor.buf);

        match dir_to_donor {
            Dir::Left => {
                // donor is to left, so keys will be less than ours, so we can't just append them
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
}

// ---------------------------------------------------------------------------------------------
//                                                              ▄▄· ▄• ▄▌▄▄▄  .▄▄ ·       ▄▄▄
//                                                             ▐█ ▌▪█▪██▌▀▄ █·▐█ ▀. ▪     ▀▄ █·
//                                                             ██ ▄▄█▌▐█▌▐▀▀▄ ▄▀▀▀█▄ ▄█▀▄ ▐▀▀▄
//  Cursor                                                     ▐███▌▐█▄█▌▐█•█▌▐█▄▪▐█▐█▌.▐▌▐█•█▌
//                                                             ·▀▀▀  ▀▀▀ .▀  ▀ ▀▀▀▀  ▀█▄▀▪.▀  ▀
// ---------------------------------------------------------------------------------------------
// NOTE: cursors do not hold any pins, pin-holding for optimization should be done at the tx level

#[derive(Clone)]
pub(super) struct Cursor {
    pub(super) btree: Btree,
    traversal:        FixedArray<(u64, u16), TRAVERSAL_LENGTH>,
    slot_idx:         u16,
    needs_page_adv:   bool,
    is_exhausted:     bool,
}

impl<'tx> Cursor {
    /// New lazily-initialized cursor
    pub(super) fn new(pgid_root: u64) -> Self {
        Self {
            btree:          Btree::from_pgid(pgid_root),
            traversal:      Traversal::new(),
            slot_idx:       0,
            needs_page_adv: false,
            is_exhausted:   false,
        }
    }

    pub(super) fn is_exhausted(&self) -> bool {
        self.is_exhausted
    }

    fn reinit(&mut self) {
        self.traversal.clear();
        self.slot_idx = 0;
        self.needs_page_adv = false;
        self.is_exhausted = false;
    }

    pub(super) fn seek<R: PageReader<'tx>, T>(
        &mut self, _tx: &R, _read_into_owned: impl FnOnce(&[u8], &[u8]) -> T,
    ) -> Result<Option<T>, PagerErr> {
        // this is complicated - we should pop the stack only as much as we need to to get to our
        // sought key
        todo!()
    }

    /// visits current entry but does not advance cursor head
    pub(super) fn peek<R: PageReader<'tx>, T>(
        &mut self, tx: &R, read_into_owned: impl FnOnce(&[u8], &[u8]) -> T,
    ) -> Result<Option<T>, PagerErr> {
        // This will only be Some if we were uninitialized
        let rhdl_opt = if self.traversal.is_empty() {
            // advance once if still uninitialized
            // Well use the rhdl it gives us, otherwise well just fetch ourself
            let Some(rhdl) = self.advance_and_check_exhausted(tx)? else {
                return Ok(None);
            };
            Some(rhdl)
        } else {
            None
        };

        if self.is_exhausted {
            return Ok(None);
        }

        let (pgid, _) = *self.traversal.last_ref();
        let rhdl = rhdl_opt.unwrap_or(tx.get_page_read(pgid)?);
        let page = BtreePage::from_buffer_ref(rhdl.buf);

        let (key, val) = page.key_val_slices_from_slot(self.slot_idx);
        Ok(Some(read_into_owned(key, val)))
    }

    /// advances then visits
    pub(super) fn next<T, R: PageReader<'tx>>(
        &mut self, tx: &R, read_into_owned: impl FnOnce(&[u8], &[u8]) -> T,
    ) -> Result<Option<T>, PagerErr> {
        let Some(rhdl) = self.advance_and_check_exhausted(tx)? else {
            return Ok(None);
        };

        let page = BtreePage::from_buffer_ref(rhdl.buf);
        let (key, val) = page.key_val_slices_from_slot(self.slot_idx);
        Ok(Some(read_into_owned(key, val)))
    }

    /// visits current entry but does not advance cursor head
    pub(super) fn advance<R: PageReader<'tx>>(&mut self, tx: &R) -> Result<(), PagerErr> {
        self.advance_and_check_exhausted(tx).map(|_| ())
    }

    // ----- helper --------------------------------------------------------------------------------

    // the first call to this fn will initialize our traversal list, and the cursor will be left on
    // the first entry of the tree (min).
    fn advance_and_check_exhausted<R: PageReader<'tx>>(
        &mut self, tx: &R,
    ) -> Result<Option<RdHdl<'tx>>, PagerErr> {
        if self.is_exhausted {
            return Ok(None);
        }

        if self.traversal.len() == 0 {
            let mut next_pgid = self.btree.root_pgid;

            if next_pgid == PGID_NULL {
                self.is_exhausted = true;
                return Ok(None);
            }

            loop {
                let rhdl = tx.get_page_read(next_pgid)?;
                let curr_page = BtreePage::from_buffer_ref(rhdl.buf);

                match curr_page.get_page_type() {
                    BtreePageType::Inner => {
                        next_pgid = pgid_from_bytes(curr_page.key_val_slices_from_slot(0).1);
                        self.traversal.push((rhdl.get_pgid(), 0));
                    }
                    BtreePageType::Leaf => {
                        self.traversal.push((rhdl.get_pgid(), SLOT_INDEX_NULL));

                        if curr_page.len() == 0 {
                            self.is_exhausted = true;
                            return Ok(None);
                        }

                        return Ok(Some(rhdl));
                    }
                }
            }
        }

        mooo_assert!(!self.is_exhausted);
        mooo_assert!(!self.traversal.is_empty());

        self.slot_idx += 1;

        let (pgid, _) = *self.traversal.last_ref();
        let rhdl = tx.get_page_read(pgid)?;
        let page = BtreePage::from_buffer_ref(rhdl.buf);

        if self.slot_idx < page.len() {
            return Ok(Some(rhdl));
        }

        // otherwise we need to advance to the next page

        loop {
            if self.traversal.len() == 1 {
                // if were at the root and would need to go to the next page then were exhausted
                self.is_exhausted = true;
                return Ok(None);
            }

            // this is if we are not root
            self.traversal.pop();
            let (pgid_parent, slot_idx) = self.traversal.last_mut();
            let rhdl_parent = tx.get_page_read(*pgid_parent)?;
            let page_parent = BtreePage::from_buffer_ref(rhdl_parent.buf);

            *slot_idx += 1;
            if *slot_idx < page_parent.len() {
                let pgid_next = pgid_from_bytes(page_parent.key_val_slices_from_slot(*slot_idx).1);
                self.traversal.push((pgid_next, 0));
                self.slot_idx = 0;
                self.needs_page_adv = false;
                break;
                // else we need to pop another level
            }
        }

        // if we popped more than once were no longer at a leaf and we need to traverse down
        // left again
        let mut pgid_next;
        loop {
            // "maybe" parent
            let (pgid_parent, _) = *self.traversal.last_ref();
            let rhdl_parent = tx.get_page_read(pgid_parent)?;
            let page_parent = BtreePage::from_buffer_ref(rhdl_parent.buf);
            if page_parent.is_leaf() {
                return Ok(Some(rhdl_parent));
            }
            pgid_next = pgid_from_bytes(page_parent.key_val_slices_from_slot(0).1);
            self.traversal.push((pgid_next, 0));
        }
    }
}

pub(super) struct BtreeMeta {
    pub(super) page_cnt_total: u64,
    pub(super) page_cnt_leaf:  u64,
    pub(super) page_cnt_inner: u64,
    pub(super) entry_cnt:      u64,
    pub(super) bytes:          u64,
}

impl AddAssign for BtreeMeta {
    fn add_assign(&mut self, rhs: Self) {
        self.page_cnt_total += rhs.page_cnt_total;
        self.page_cnt_leaf += rhs.page_cnt_leaf;
        self.page_cnt_inner += rhs.page_cnt_inner;
        self.entry_cnt += rhs.entry_cnt;
        self.bytes += rhs.bytes;
    }
}
