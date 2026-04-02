use crate::{
    buffer::pager::{FrameRef, Pager},
    io,
    page::{PageCommon, PageHeap, PageSuperblock, SUPERBLOCK_PAGE_ID},
};

pub(crate) struct Storage {
    pager: Pager,
}

impl Storage {
    #[must_use]
    pub(crate) async fn new(iodoer: Box<dyn io::IODoer>, buffer_frame_count: usize) -> Self {
        let pager = Pager::new(iodoer, buffer_frame_count);

        {
            let frame_ref = pager.get_page_id(SUPERBLOCK_PAGE_ID).await.expect("todo");
            frame_ref.leak();
            let mut frame_guard = frame_ref.write_lock().await.expect("todo haha");
            let mut superblock = PageSuperblock::from_buffer(&mut frame_guard.buffer);
            superblock.initialize();
        }

        Self { pager }
    }

    async fn superblock(&self) -> FrameRef<'_> {
        self.pager.get_page_id(SUPERBLOCK_PAGE_ID).await.unwrap()
    }

    pub(crate) async fn load_existing(iodoer: Box<dyn io::IODoer>, buffer_frame_count: usize) -> Self {
        let pager = Pager::new(iodoer, buffer_frame_count);

        {
            let superblock_ref = pager.get_page_id(SUPERBLOCK_PAGE_ID).await.unwrap();
            let mut superblock_guard = superblock_ref.write_lock().await.unwrap();
            let superblock_page = PageSuperblock::from_buffer(&mut superblock_guard.buffer);
            assert_eq!(superblock_page.checksum(), superblock_page.compute_checksum()); // TODO
        }

        return Self { pager };
    }

    pub(crate) async fn get_page(&self, page_id: u64) -> FrameRef<'_> {
        self.pager.get_page_id(page_id).await.unwrap()
    }

    /// Very well may return a dirty page
    pub(crate) async fn get_free_page(&self) -> (u64, FrameRef<'_>) {
        let _superblock_fr = self.superblock().await;
        let mut _superblock_g = _superblock_fr.write_lock().await.unwrap();
        let mut superblock = PageSuperblock::from_buffer(&mut _superblock_g.buffer);

        let free_list_root = superblock.free_list_next();

        let page_id = if free_list_root == SUPERBLOCK_PAGE_ID {
            let page = superblock.next_page_id();
            superblock.set_next_page_id(superblock.next_page_id() + 1);
            page
        } else {
            let frame_ref = self.pager.get_page_id(free_list_root).await.expect("todo");
            let frame_guard = frame_ref.read_lock().await.expect("todo: frame load error");
            let next_free = PageCommon::from_buffer_ref(&frame_guard.buffer).next_free();
            drop(frame_guard);

            superblock.set_free_list_next(next_free);
            superblock.set_free_list_count(superblock.free_list_count() - 1);

            free_list_root
        };

        (page_id, self.pager.get_page_id(page_id).await.expect("todo"))
    }

    pub(crate) async fn free_page(&self, page_id: u64) {
        let _superblock_fr = self.superblock().await;
        let mut _superblock_g = _superblock_fr.write_lock().await.unwrap();
        let mut superblock = PageSuperblock::from_buffer(&mut _superblock_g.buffer);

        tracing::trace!("free: {} {} {}", page_id, superblock.free_list_next(), superblock.free_list_count());

        if superblock.free_list_next() == SUPERBLOCK_PAGE_ID {
            superblock.set_free_list_next(page_id);
            superblock.set_free_list_count(1);
        } else {
            // if theres already a page in the list, we need to make this page point to it
            let frame_ref = self.pager.get_page_id(page_id).await.expect("todo");
            let mut frame_guard = frame_ref.write_lock().await.expect("huh?");

            // TODO write PageFree
            let mut page = PageHeap::new_with_buffer(&mut frame_guard.buffer, page_id, 0, 0);
            page.set_next_free(superblock.free_list_next());

            superblock.set_free_list_next(page_id);
            superblock.set_free_list_count(superblock.free_list_count() + 1);
        }
    }
}
