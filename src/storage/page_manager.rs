use std::sync::Arc;

use crate::{
    page,
    storage::{
        frame::{FrameRef, FrameWriteGuard},
        page_buffer::PageBuffer,
    },
};

pub(crate) struct PageManager {
    page_buffer: PageBuffer,
}

impl PageManager {
    /// Initializes a new database - NOTE Destructive!
    pub(crate) fn new(io: Arc<dyn crate::io::IOFactory>, frame_count: usize) -> Self {
        let page_buffer = PageBuffer::new(io, frame_count);
        let page_manager = PageManager { page_buffer };

        let (frame_ref, mut frame_guard) = page_manager
            .page_buffer
            .get_page_new(page::SUPERBLOCK_PAGE_ID)
            .expect("Couldn't get page for superblock");

        frame_ref.leak(); // leak a pin on this frame so it always stays in the cache
        let mut superblock = page::Superblock::from_buffer(&mut frame_guard.buffer);
        superblock.initialize();
        frame_guard.dirty = true;

        drop(frame_ref);
        drop(frame_guard);

        page_manager
    }

    fn superblock(&self) -> Result<FrameRef<'_>, std::io::ErrorKind> {
        self.page_buffer.get_page_existing(page::SUPERBLOCK_PAGE_ID)
    }

    pub(crate) fn get_page_existing(&self, page_id: u64) -> Result<FrameRef<'_>, std::io::ErrorKind> {
        self.page_buffer.get_page_existing(page_id)
    }

    /// NOTE This will often give a dirty page
    pub(crate) fn get_page_new(&self) -> Result<(FrameRef<'_>, FrameWriteGuard<'_>), std::io::ErrorKind> {
        let super_ref = self.superblock()?;
        let mut super_guard = super_ref.write_lock();
        let mut super_page = page::Superblock::from_buffer(&mut super_guard.buffer);

        match super_page.alloc_free_list_count() {
            0 => {
                // we have no free pages in our LL, so we just bump alloc
                let next_free_page_id = super_page.alloc_bump_next_id();
                super_page.alloc_increment_bump();
                super_guard.dirty = true;
                self.page_buffer.get_page_new(next_free_page_id)
            }
            free_list_count => {
                // we have some free pages in our LL
                let next_free_page_id = super_page.alloc_free_list_next();
                let free_ref = self.page_buffer.get_page_existing(next_free_page_id)?;

                // this should all be ok because were holding an excl lock on the superblock this
                // whole time
                let free_guard = free_ref.write_lock();
                let free_page = page::Common::from_buffer_ref(&free_guard.buffer);
                let next_next_free_page_id = free_page.next_free();

                super_page.set_alloc_free_list_next(next_next_free_page_id);
                super_page.set_alloc_free_list_count(free_list_count - 1);
                super_guard.dirty = true;

                Ok((free_ref, free_guard))
            }
        }
    }

    /// Frees a page so it can be reused, will add to the superblocks free-list
    pub(crate) fn free_page(&self, page_id: u64) -> Result<(), std::io::ErrorKind> {
        // concurrency wise this should be safe even if we do something dumb,
        // because even though we free it according to the superblock, the page-buffer wont reaward
        // it out to somebody until it is evictable - so if there are latent pinners this wont be
        // "handed out from under them"
        let super_ref = self.superblock()?;
        let mut super_guard = super_ref.write_lock();
        let mut super_page = page::Superblock::from_buffer(&mut super_guard.buffer);

        let free_ref = self.page_buffer.get_page_existing(page_id)?;
        let mut free_guard = free_ref.write_lock();
        let mut free_page = page::Common::from_buffer(&mut free_guard.buffer);

        match super_page.alloc_free_list_count() {
            0 => {
                // we have no free pages in our LL, well initialize the list with this page
                free_page.set_next_free(page::SUPERBLOCK_PAGE_ID);
                free_guard.dirty = true;

                super_page.set_alloc_free_list_next(page_id);
                super_page.set_alloc_free_list_count(1);
                super_guard.dirty = true;
            }
            free_list_count => {
                // we have some free pages in our LL
                let current_next_free = super_page.alloc_free_list_next();

                // this is the page that is being freed
                // swap newly-freed page to point to old head of list
                free_page.set_next_free(current_next_free);
                free_guard.dirty = true;

                // swap head of list to point to newly-freed page
                super_page.set_alloc_free_list_next(page_id);
                super_page.set_alloc_free_list_count(free_list_count + 1);
                super_guard.dirty = true;
            }
        }

        Ok(())
    }
}

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::{io::mem_io::MemIO, page};

    fn make_pm(frame_count: usize) -> PageManager {
        let pm = PageManager::new(Arc::new(MemIO::new()), frame_count);
        pm.page_buffer.init_thread();
        pm
    }

    /// Returns (next_page_id, free_list_count, free_list_next) from the superblock.
    fn superblock_state(pm: &PageManager) -> (u64, u64, u64) {
        let super_ref = pm.superblock().unwrap();
        let mut guard = super_ref.write_lock();
        let sb = page::Superblock::from_buffer(&mut guard.buffer);
        (sb.alloc_bump_next_id(), sb.alloc_free_list_count(), sb.alloc_free_list_next())
    }

    #[test]
    fn superblock_initializes_correctly() {
        let pm = make_pm(4);
        let (next_page_id, free_list_count, _) = superblock_state(&pm);
        assert_eq!(next_page_id, 1, "first allocatable page should be 1");
        assert_eq!(free_list_count, 0, "free list should start empty");
    }

    #[test]
    fn fresh_allocations_use_bump_allocator() {
        let pm = make_pm(8);

        let (_r1, g1) = pm.get_page_new().unwrap();
        let (_r2, g2) = pm.get_page_new().unwrap();
        let (_r3, g3) = pm.get_page_new().unwrap();

        assert_eq!(g1.page_id, 1);
        assert_eq!(g2.page_id, 2);
        assert_eq!(g3.page_id, 3);

        let (next_page_id, free_list_count, _) = superblock_state(&pm);
        assert_eq!(next_page_id, 4);
        assert_eq!(free_list_count, 0);
    }

    #[test]
    fn freed_page_is_reused_before_bump() {
        let pm = make_pm(8);

        let (r1, g1) = pm.get_page_new().unwrap();
        let freed_id = g1.page_id; // page 1
        drop(g1);
        drop(r1);

        pm.free_page(freed_id).unwrap();

        let (_, g2) = pm.get_page_new().unwrap();
        assert_eq!(g2.page_id, freed_id, "freed page should be reclaimed from free list");

        // bump allocator should not have advanced past 2
        let (next_page_id, free_list_count, _) = superblock_state(&pm);
        assert_eq!(next_page_id, 2, "bump allocator must not advance when free list supplies a page");
        assert_eq!(free_list_count, 0);
    }

    #[test]
    fn free_list_count_tracks_frees_and_allocs() {
        let pm = make_pm(16);

        let (r1, g1) = pm.get_page_new().unwrap();
        let (r2, g2) = pm.get_page_new().unwrap();
        let (r3, g3) = pm.get_page_new().unwrap();
        let (id1, id2, id3) = (g1.page_id, g2.page_id, g3.page_id);
        drop(g1);
        drop(r1);
        drop(g2);
        drop(r2);
        drop(g3);
        drop(r3);

        pm.free_page(id1).unwrap();
        assert_eq!(superblock_state(&pm).1, 1);

        pm.free_page(id2).unwrap();
        assert_eq!(superblock_state(&pm).1, 2);

        pm.free_page(id3).unwrap();
        assert_eq!(superblock_state(&pm).1, 3);

        let (_, ga) = pm.get_page_new().unwrap();
        drop(ga);
        assert_eq!(superblock_state(&pm).1, 2);

        let (_, gb) = pm.get_page_new().unwrap();
        drop(gb);
        assert_eq!(superblock_state(&pm).1, 1);

        let (_, gc) = pm.get_page_new().unwrap();
        drop(gc);
        assert_eq!(superblock_state(&pm).1, 0);
    }

    #[test]
    fn free_list_is_lifo() {
        let pm = make_pm(16);

        println!("allocating");

        let (id1, id2, id3) = {
            let (_, g1) = pm.get_page_new().unwrap();
            let (_, g2) = pm.get_page_new().unwrap();
            let (_, g3) = pm.get_page_new().unwrap();
            (g1.page_id, g2.page_id, g3.page_id)
        };

        println!("freeing");

        // free 1, 2, 3 — expect them back as 3, 2, 1
        pm.free_page(id1).unwrap();
        pm.free_page(id2).unwrap();
        pm.free_page(id3).unwrap();

        println!("re-allocating");

        let (_, ga) = pm.get_page_new().unwrap();
        assert_eq!(ga.page_id, id3);
        drop(ga);

        let (_, gb) = pm.get_page_new().unwrap();
        assert_eq!(gb.page_id, id2);
        drop(gb);

        assert_eq!(superblock_state(&pm).1, 1, "should be just one in free list");

        let (_, gc) = pm.get_page_new().unwrap();
        assert_eq!(gc.page_id, id1);
        drop(gc);

        println!("done");

        assert_eq!(superblock_state(&pm).1, 0, "free list should be empty after draining");
    }

    #[test]
    fn bump_allocator_resumes_after_free_list_drained() {
        let pm = make_pm(8);

        // alloc page 1, free it, reclaim it
        let (r1, g1) = pm.get_page_new().unwrap();
        let id1 = g1.page_id;
        drop(g1);
        drop(r1);
        pm.free_page(id1).unwrap();
        let (_, reclaimed) = pm.get_page_new().unwrap();
        assert_eq!(reclaimed.page_id, id1);
        drop(reclaimed);

        // free list now empty; next alloc must come from the bump allocator
        let (_, g2) = pm.get_page_new().unwrap();
        assert_eq!(g2.page_id, 2, "bump allocator should resume at next unallocated id");
    }

    /// Exercises multiple interleaved alloc/free operations to verify that the free list
    /// and bump allocator interact correctly throughout a realistic usage pattern.
    #[test]
    fn interleaved_alloc_free_cycles() {
        let pm = make_pm(16);

        // Allocate A (1) and B (2).
        let (r_a, g_a) = pm.get_page_new().unwrap();
        let (r_b, g_b) = pm.get_page_new().unwrap();
        let (id_a, id_b) = (g_a.page_id, g_b.page_id);
        assert_eq!((id_a, id_b), (1, 2));
        drop(g_a);
        drop(r_a);

        // Free A → list: [A], count=1.
        pm.free_page(id_a).unwrap();
        assert_eq!(superblock_state(&pm).1, 1);

        // Alloc → should pull A back from the free list (count 1→0).
        let (_, g) = pm.get_page_new().unwrap();
        assert_eq!(g.page_id, id_a, "should reclaim A from free list");
        drop(g);
        assert_eq!(superblock_state(&pm).1, 0);

        // Free list is empty; next alloc must come from the bump allocator at page 3.
        let (_, g) = pm.get_page_new().unwrap();
        assert_eq!(g.page_id, 3);
        let id_c = g.page_id;
        drop(g);

        // Free B then C — list becomes [C→B], count=2.
        drop(g_b);
        drop(r_b);
        pm.free_page(id_b).unwrap();
        pm.free_page(id_c).unwrap();
        assert_eq!(superblock_state(&pm).1, 2);

        // Drain free list: LIFO order must give C then B.
        let (_, g) = pm.get_page_new().unwrap();
        assert_eq!(g.page_id, id_c);
        drop(g);
        let (_, g) = pm.get_page_new().unwrap();
        assert_eq!(g.page_id, id_b);
        drop(g);

        // Free list empty; bump allocator should continue from 4.
        let (_, g) = pm.get_page_new().unwrap();
        assert_eq!(g.page_id, 4);
        let (_, count, _) = superblock_state(&pm);
        assert_eq!(count, 0);
    }

    /// N threads each allocate M pages concurrently while all holding their FrameRefs.
    /// Every returned page ID must be unique.
    #[test]
    fn concurrent_allocations_are_unique() {
        use std::sync::Mutex;

        const THREADS: usize = 8;
        const PAGES_PER_THREAD: usize = 16;
        // enough frames so no eviction is needed: 1 superblock + all data pages
        let pm = make_pm(1 + THREADS * PAGES_PER_THREAD);
        let collected = Mutex::new(Vec::<u64>::new());

        std::thread::scope(|s| {
            for _ in 0..THREADS {
                s.spawn(|| {
                    pm.page_buffer.init_thread();
                    // Keep all refs alive so each frame slot is held for the full duration.
                    let mut refs = Vec::new();
                    let mut ids = Vec::new();
                    for _ in 0..PAGES_PER_THREAD {
                        let (r, g) = pm.get_page_new().unwrap();
                        ids.push(g.page_id);
                        refs.push((r, g));
                    }
                    collected.lock().unwrap().extend_from_slice(&ids);
                });
            }
        });

        let mut ids = collected.into_inner().unwrap();
        assert_eq!(ids.len(), THREADS * PAGES_PER_THREAD);
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), THREADS * PAGES_PER_THREAD, "duplicate page IDs allocated");
    }

    /// Buffer is intentionally sized so that a second thread cannot get a frame until the
    /// first thread releases one. Verifies that `scan_for_eviction_candidate` correctly
    /// blocks (spins) and is unblocked when a pin is released.
    #[test]
    fn allocation_waits_for_frame_release() {
        // Exactly 1 superblock frame + 2 data frames = 3 total.
        let pm = make_pm(3);

        // Pin both data frames from this thread.
        let (r1, g1) = pm.get_page_new().unwrap(); // frame for page 1
        let (r2, g2) = pm.get_page_new().unwrap(); // frame for page 2
        // Every frame is now pinned; the spawned thread will spin until we release one.

        std::thread::scope(|s| {
            s.spawn(|| {
                pm.page_buffer.init_thread();
                // This call enters scan_for_eviction_candidate and spins until
                // the main thread drops r1, making that frame available.
                let (_r3, g3) = pm.get_page_new().unwrap();
                assert!(g3.page_id >= 1, "must receive a valid data page");
            });

            // Release one pin so the spawned thread can proceed.
            // drop guard first (releases write lock), then ref (decrements pin to 0).
            drop(g1);
            drop(r1);
            // std::thread::scope waits here for the spawned thread to finish.
        });

        drop(g2);
        drop(r2);
    }

    /// Concurrent alloc + free loop: verifies that no page ID is live in two threads
    /// at the same time — i.e., get_page_new never grants a page that is still allocated.
    #[test]
    fn no_double_grant_under_concurrent_alloc_free() {
        use std::collections::HashSet;
        use std::sync::Mutex;

        const THREADS: usize = 4;
        const OPS_PER_THREAD: usize = 32;
        // generous frame count: 1 superblock + room for all threads to hold a page
        // simultaneously, plus plenty of headroom for pages that are in the buffer
        // but waiting to be evicted
        let pm = make_pm(1 + THREADS * (OPS_PER_THREAD + 1));

        // The invariant: a page ID that has been allocated but not yet freed must not
        // appear in any concurrent get_page_new.
        let live: Mutex<HashSet<u64>> = Mutex::new(HashSet::new());

        std::thread::scope(|s| {
            for _ in 0..THREADS {
                s.spawn(|| {
                    pm.page_buffer.init_thread();
                    for _ in 0..OPS_PER_THREAD {
                        let (r, g) = pm.get_page_new().unwrap();
                        let id = g.page_id;

                        // Must not already be live — that would mean a double-grant.
                        assert!(
                            live.lock().unwrap().insert(id),
                            "page {id} was given out while still live in another thread"
                        );

                        // Unpin the frame, mark as no longer live, then hand it to the free list.
                        // Between unpin and free_page the page cannot be re-granted (it's not in
                        // the free list yet and the bump allocator never reuses IDs).
                        drop(g);
                        drop(r);
                        live.lock().unwrap().remove(&id);
                        pm.free_page(id).unwrap();
                    }
                });
            }
        });
    }
}
