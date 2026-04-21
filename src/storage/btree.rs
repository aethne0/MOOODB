use std::mem::MaybeUninit;

use crate::storage::page_btree::BtreePageType;

use super::page_base::U64Entry;
use super::page_btree::BtreePage;
use super::pager::*;
use super::PagerErr;
use super::PAGE_ID_NULL;

/// It is the responsibility of the caller to update anything that may point to this `root_page_id`
pub(super) struct Btree(u64);
impl Btree {
    // ------------ Constructors -------------------------------------------------------------------

    #[must_use]
    pub(crate) fn from_root_id(root_page_id: u64) -> Self {
        Self(root_page_id)
    }

    pub(crate) fn root_id(&self) -> u64 {
        self.0
    }

    // ------------ Get ----------------------------------------------------------------------------

    pub(crate) fn get<'tx, R: PgrReader<'tx>>(
        &self, handle: &R, key: &[u8],
    ) -> Result<Option<U64Entry>, PagerErr> {
        let mut page_id = self.0;

        loop {
            let page = BtreePage::from_buffer_ref(handle.get_page_read(page_id)?.buf);

            if page.is_leaf() {
                return Ok(page.get(key));
            }

            page_id = page.get_traversal_next_page(key).unwrap().get();
        }
    }

    // ------------ New ----------------------------------------------------------------------------

    pub(crate) fn new<'tx, R: PgrReader<'tx> + PgrWriter<'tx>>(tx: &R) -> Result<Btree, PagerErr> {
        let w_hdl = tx.get_page_alloc()?;
        let page_id = w_hdl.get_page_id();
        BtreePage::new_with_buffer(w_hdl.buf, PAGE_ID_NULL, BtreePageType::Leaf);
        Ok(Self::from_root_id(page_id))
    }

    // ------------ Insert -------------------------------------------------------------------------

    pub(crate) fn insert<'tx, R: PgrReader<'tx> + PgrWriter<'tx>>(
        &mut self, tx: &R, key: &[u8], value: U64Entry,
    ) -> Result<(), PagerErr> {
        let mut new_root_page_id = self.0;
        let mut next_page_id = self.0;
        let mut page_stack = PageStack::new();

        loop {
            let w_hdl = tx.get_page_write(next_page_id)?;
            let curr_page_id = w_hdl.get_page_id();
            let mut curr_page = BtreePage::from_buffer(w_hdl.buf);

            if page_stack.len() == 0 {
                // update root_id with the first page we touch (top)
                new_root_page_id = curr_page_id;
            }

            if curr_page.is_leaf() {
                // page.page_id.set(page_id);
                let had_space = curr_page.insert(key, value);

                if !had_space {
                    let right_w_hdl = tx.get_page_alloc()?;
                    let right_page_id = right_w_hdl.get_page_id();
                    // this stuff will be correct assuming we dont split
                    let mut right_page = BtreePage::new_with_buffer(
                        right_w_hdl.buf,
                        curr_page.parent_id.get(),
                        curr_page.get_page_type(),
                    );

                    // redistribute
                    curr_page.redistribute_into(&mut right_page);

                    if curr_page.parent_id == PAGE_ID_NULL {
                        // if we are the root
                        let parent_w_hdl = tx.get_page_alloc()?;
                        let parent_page_id = parent_w_hdl.get_page_id();
                        let mut parent_page = BtreePage::new_with_buffer(
                            parent_w_hdl.buf,
                            PAGE_ID_NULL,
                            BtreePageType::Inner,
                        );

                        parent_page
                            .insert_unordered(curr_page.entry_at_slot(0).0, curr_page_id.into());
                        curr_page.parent_id.set(parent_page_id);

                        parent_page
                            .insert_unordered(right_page.entry_at_slot(0).0, right_page_id.into());
                        right_page.parent_id.set(parent_page_id);

                        new_root_page_id = parent_page_id;
                    } else {
                        // this is the case where we had a inner-node parent; we are not the root
                        let parent_w_hdl = tx.get_page_write(curr_page.parent_id.get())?;
                        let parent_page_id = parent_w_hdl.get_page_id();
                        let mut parent_page = BtreePage::from_buffer(parent_w_hdl.buf);

                        let had_space =
                            parent_page.insert(right_page.entry_at_slot(0).0, right_page_id.into());
                        if !had_space {
                            todo!(
                                "inner page {} already had {} entries",
                                parent_page_id,
                                parent_page.len()
                            );
                        }
                    }
                }

                break;
            } else {
                next_page_id = curr_page.get_traversal_next_page(key).unwrap().get(); // todo
                page_stack.push(curr_page_id);
            }
        }

        let mut prev_page_id = PAGE_ID_NULL;
        for page_id in page_stack {
            // this is just for setting parent-pointers
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
