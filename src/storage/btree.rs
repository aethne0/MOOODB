use super::pages::BtreePage;
use super::pages::U64Entry;
use super::rw_manager::PageReader;
use super::rw_manager::PageWriter;

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

            if !page.is_leaf() {
                todo!()
            }

            return Ok(page.get(key));
        }
    }
}

impl<'a, R: PageReader + PageWriter> Btree<'a, R> {
    fn insert(_key: &[u8], _value: &[u8]) -> Result<(), std::io::ErrorKind> {
        todo!()
    }
}
