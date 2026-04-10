use super::pages::BtreePage;
use super::pages::U64Entry;
use super::rw_manager::PageAllocator;
use super::rw_manager::PageReader;

struct Btree<'a, R: PageReader> {
    root_page_id: u64,
    handle: &'a R,
}

impl<'a, R: PageReader> Btree<'a, R> {
    fn get(&self, key: &[u8]) -> Result<Option<U64Entry>, std::io::ErrorKind> {
        let mut next_page_id = self.root_page_id;

        loop {
            let guard = self.handle.get_page_read(next_page_id)?;
            let page = BtreePage::from_buffer_ref(guard.buffer);

            if page.is_leaf() {
                return Ok(page.get(key));
            } else {
                if let Some(next_ptr_entry) = page.get_first_slot_ge_key(key) {
                    next_page_id = next_ptr_entry.get();
                } else {
                    return Ok(None);
                };
            }
        }
    }
}

impl<'a, R: PageReader + PageAllocator> Btree<'a, R> {
    fn insert(_key: &[u8], _value: &[u8]) -> Result<(), std::io::ErrorKind> {
        todo!()
    }
}
