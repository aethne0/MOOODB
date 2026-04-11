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
    use crate::sync::*;
    use shuttle::sync::*;

    fn check(f: impl Fn() + Send + Sync + 'static) {
        let scheduler = shuttle::scheduler::RandomScheduler::new(2000);
        let mut config = shuttle::Config::default();
        config.failure_persistence = shuttle::FailurePersistence::None;
        config.max_steps = shuttle::MaxSteps::FailAfter(1_000_000_000);
        let runner = shuttle::Runner::new(scheduler, config);
        runner.run(f);
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

    /// Two threads, 2 frames, 3 pages on disk.
    /// Each thread reads two pages sequentially; the narrow pool forces eviction
    /// mid-flight and the threads converge on page 2 from different directions,
    /// exercising both the eviction path and the same-page adoption path together.
    #[test]
    fn eviction_under_concurrent_reads_2() {
        check(|| {
            const PAGECNT: u64 = 10;
            const THREADS: u64 = 16;
            const ITERS: u64 = 16;
            let bump = Arc::new(AtomicU64::new(0));
            let tmp = make_page_file(PAGECNT);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(THREADS as usize * 2 , file));

            let mut handles = vec![];
            for thread_idx in 0..THREADS {
                let b = bump.clone();
                let p = Arc::clone(&pager);
                let h = shuttle::thread::spawn(move || {
                    for iter_idx in 0..ITERS {
                        for page_idx in 0..PAGECNT {
                            {
                                let g1 =
                                    p.get_page_existing((page_idx + thread_idx) % PAGECNT).unwrap();
                                let g2 = p
                                    .get_page_existing((page_idx + thread_idx + 1) % PAGECNT)
                                    .unwrap();
                            }
                            {
                                let g3 = p
                                    .get_page_new(1_000_000 + b.fetch_add(1, Ordering::Relaxed))
                                    .unwrap();
                                g3.commit();
                            }
                        }
                    }
                });
                handles.push(h);
            }

            for h in handles {
                h.join();
            }
        });
    }
}
