use crate::storage::pages::checksum;
use crate::storage::PAGE_SIZE;

/// Write `page_count` pages with valid checksums to a fresh temp file.
fn make_page_file(page_count: u64) -> tempfile::NamedTempFile {
    use std::io::Write;
    let mut f = tempfile::NamedTempFile::new().unwrap();
    for _ in 0..page_count {
        let mut buf = [0u8; PAGE_SIZE];
        checksum::set(&mut buf);
        f.write_all(&buf).unwrap();
    }
    f
}

// shuttle
#[cfg(all(shuttle, not(loom)))]
mod shuttle_tests {
    use super::*;
    use crate::storage::pager::Pager;
    use shuttle::sync::Arc;

    fn check(f: impl Fn() + Send + Sync + 'static) {
        shuttle::check_random(f, 200);
    }

    /// N threads all request the same page concurrently.
    /// Exercises the "another thread beat us to loading this page" adoption path in
    /// `get_page_existing`.
    #[test]
    fn concurrent_read_same_page() {
        check(|| {
            let tmp = make_page_file(1);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(4, file));

            let handles: Vec<_> = (0..3)
                .map(|_| {
                    let p = Arc::clone(&pager);
                    shuttle::thread::spawn(move || {
                        drop(p.get_page_existing(0).unwrap());
                    })
                })
                .collect();

            for h in handles {
                h.join().unwrap();
            }
        });
    }

    /// Each thread reads a distinct page; no sharing, no eviction pressure.
    /// Verifies that independent shard locks don't interfere.
    #[test]
    fn concurrent_read_distinct_pages() {
        check(|| {
            let tmp = make_page_file(3);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(8, file));

            let handles: Vec<_> = (0u64..3)
                .map(|page_id| {
                    let p = Arc::clone(&pager);
                    shuttle::thread::spawn(move || {
                        drop(p.get_page_existing(page_id).unwrap());
                    })
                })
                .collect();

            for h in handles {
                h.join().unwrap();
            }
        });
    }

    /// Single thread, 2 frames, 3 new pages: the third `get_page_new` must evict a
    /// dirty frame and flush it to disk before it can reuse the slot.
    #[test]
    fn eviction_flushes_dirty_frame() {
        check(|| {
            let tmp = make_page_file(0); // empty file; pages are created, not read
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(2, file));
            let p = Arc::clone(&pager);

            shuttle::thread::spawn(move || {
                p.get_page_new(0).unwrap().commit();
                p.get_page_new(1).unwrap().commit();
                // Must evict and write out page 0 or 1 (both dirty) before this succeeds.
                p.get_page_new(2).unwrap().commit();
            })
            .join()
            .unwrap();
        });
    }

    /// Two threads, 2 frames, 3 pages on disk.
    /// Each thread reads two pages sequentially; the narrow pool forces eviction
    /// mid-flight and the threads converge on page 2 from different directions,
    /// exercising both the eviction path and the same-page adoption path together.
    #[test]
    fn eviction_under_concurrent_reads() {
        check(|| {
            let tmp = make_page_file(3);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(2, file));

            let p1 = Arc::clone(&pager);
            let p2 = Arc::clone(&pager);

            // Each thread holds at most one guard at a time so the pool never
            // fully deadlocks (both frames simultaneously pinned while a third
            // load is attempted).
            let h1 = shuttle::thread::spawn(move || {
                drop(p1.get_page_existing(0).unwrap());
                drop(p1.get_page_existing(2).unwrap());
            });
            let h2 = shuttle::thread::spawn(move || {
                drop(p2.get_page_existing(1).unwrap());
                drop(p2.get_page_existing(2).unwrap());
            });

            h1.join().unwrap();
            h2.join().unwrap();
        });
    }
}

// loom
// Tip: set LOOM_MAX_BRANCHES=100000 if model checking is too slow.
#[cfg(loom)]
mod loom_tests {
    use super::*;
    use crate::storage::pager::Pager;
    use loom::sync::Arc;

    /// Two threads race to load the same page from disk.
    /// Exhaustively verifies that exactly one issues the I/O and the other
    /// correctly adopts the already-loaded frame.
    #[test]
    fn two_threads_read_same_page() {
        loom::model(|| {
            let tmp = make_page_file(1);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(4, file));

            let p1 = Arc::clone(&pager);
            let p2 = Arc::clone(&pager);

            let h1 = loom::thread::spawn(move || drop(p1.get_page_existing(0).unwrap()));
            let h2 = loom::thread::spawn(move || drop(p2.get_page_existing(0).unwrap()));

            h1.join().unwrap();
            h2.join().unwrap();
        });
    }

    /// Two threads load different pages simultaneously.
    /// Verifies that distinct shard locks don't cause spurious serialisation or
    /// double-eviction of the same frame.
    #[test]
    fn two_threads_read_different_pages() {
        loom::model(|| {
            let tmp = make_page_file(2);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(4, file));

            let p1 = Arc::clone(&pager);
            let p2 = Arc::clone(&pager);

            let h1 = loom::thread::spawn(move || drop(p1.get_page_existing(0).unwrap()));
            let h2 = loom::thread::spawn(move || drop(p2.get_page_existing(1).unwrap()));

            h1.join().unwrap();
            h2.join().unwrap();
        });
    }

    /// Exactly 2 frames, 2 threads each wanting a different page.
    /// Both threads must scan for an eviction candidate concurrently; the
    /// `pins != 1` recheck inside `get_free_frame` guards against two threads
    /// selecting the same frame — this model exhaustively verifies that guard.
    #[test]
    fn eviction_candidate_scan_race() {
        loom::model(|| {
            let tmp = make_page_file(2);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(2, file));

            let p1 = Arc::clone(&pager);
            let p2 = Arc::clone(&pager);

            let h1 = loom::thread::spawn(move || drop(p1.get_page_existing(0).unwrap()));
            let h2 = loom::thread::spawn(move || drop(p2.get_page_existing(1).unwrap()));

            h1.join().unwrap();
            h2.join().unwrap();
        });
    }
}
