use std::mem::MaybeUninit;

use super::manager::PageAlloc;
use super::manager::PageReader;
use super::pages::BtreePage;
use super::pages::U64Entry;
use super::StorageError;
use super::PAGE_ID_NULL;

// ------------ Get ----------------------------------------------------------------------------
pub(crate) fn get<'tx, R: PageReader<'tx>>(
    root_page_id: u64, handle: &R, key: &[u8],
) -> Result<Option<U64Entry>, StorageError> {
    let mut page_id = root_page_id;

    loop {
        let page = BtreePage::from_buffer_ref(handle.get_page_read(page_id)?.buffer());

        if page.is_leaf() {
            return Ok(page.get(key));
        }

        page_id = page.get_first_slot_ge_key(key).unwrap().get();
    }
}

// ------------ New ----------------------------------------------------------------------------
pub(crate) fn new<'tx, R: PageReader<'tx> + PageAlloc<'tx>>(
    handle: &mut R,
) -> Result<u64, StorageError> {
    let (frame, page_id) = handle.get_page_alloc()?;
    BtreePage::new_with_buffer(frame.buffer(), page_id, PAGE_ID_NULL, PAGE_ID_NULL);
    Ok(page_id)
}

// ------------ Insert -------------------------------------------------------------------------
pub(crate) fn insert<'tx, R: PageReader<'tx> + PageAlloc<'tx>>(
    root_page_id: u64, handle: &mut R, key: &[u8], value: U64Entry,
) -> Result<u64, StorageError> {
    let mut new_root_page_id = root_page_id;
    let mut next_page_id = root_page_id;
    let mut page_stack = PageStack::new();

    let had_space = loop {
        let (frame, page_id) = handle.get_page_write(next_page_id)?;
        let mut page = BtreePage::from_buffer(frame.buffer());

        if page_stack.len() == 0 {
            // update root_id with the first page we touch (top)
            new_root_page_id = page_id;
        }

        if page.is_leaf() {
            break page.insert(key, value);
        } else {
            next_page_id = page.get_first_slot_ge_key(key).unwrap().get(); // todo
            page_stack.push(page_id);
        }
    };

    let mut prev_page_id = PAGE_ID_NULL;
    for page_id in page_stack {
        let (frame, found_page_id) = handle.get_page_write(page_id)?;
        assert!(page_id == found_page_id, "new pages should already be allocated");
        let mut page = BtreePage::from_buffer(frame.buffer());
        page.page_id.set(page_id);
        page.parent_id.set(prev_page_id);
        prev_page_id = page_id;
    }

    if !had_space {
        todo!()
    }

    Ok(new_root_page_id)
}

// ------------ Delete -------------------------------------------------------------------------
// pub(crate) fn delete( key: &[u8]) -> U64Entry {
//     todo!()
// }

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

#[cfg(test)]
mod test {
    use crate::storage::btree;
    use crate::storage::manager::Durability;
    use crate::storage::manager::TxManager;

    #[test]
    fn btree_inserts() {
        let file = tempfile::tempfile().unwrap();
        let mgr = TxManager::new(32, file);

        let page_id = {
            let mut tx = mgr.write_tx();

            let mut page_id = btree::new(&mut tx).unwrap();
            page_id = btree::insert(page_id, &mut tx, b"asd", 152.into()).unwrap();
            page_id = btree::insert(page_id, &mut tx, b"zxc", 642.into()).unwrap();
            page_id = btree::insert(page_id, &mut tx, b"rewt", 324.into()).unwrap();

            tx.commit(Durability::Sync).unwrap();
            page_id
        };

        let tx = mgr.read_tx();

        let res = btree::get(page_id, &tx, b"rewt").unwrap();
        assert!(res.is_some_and(|val| val.get() == 324));
    }
}
