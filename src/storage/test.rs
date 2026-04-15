use crate::storage::PAGE_SIZE;
use crate::storage::pages::checksum;

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
            const THREADS: u64 = 8;
            const ITERS: u64 = 8;
            let bump = Arc::new(AtomicU64::new(0));
            let tmp = make_page_file(PAGECNT);
            let file = tmp.reopen().unwrap();
            let pager = Arc::new(Pager::new(THREADS as usize * 2, file));

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

/*
use std::sync::atomic::{AtomicBool, Ordering as StdOrdering};
use std::sync::Arc;
use std::sync::Barrier;
use super::manager::TxManager;
use super::manager::PageReader;
use super::manager::PageAlloc;
use super::manager::Durability;

use crate::storage::PAGE_SIZE_U16;

fn make_manager(frames: usize) -> TxManager {
    let file = tempfile::tempfile().unwrap();
    TxManager::new(frames, file, PAGE_SIZE_U16)
}

// -------------------------------------------------------------------------
// Basic correctness
// -------------------------------------------------------------------------

/// Fresh manager: first read_tx should see tx_id == 0.
#[test]
fn initial_tx_id_is_zero() {
    let mgr = make_manager(8);
    let rtx = mgr.read_tx();
    assert_eq!(rtx.superblock_snapshot.tx_id.get(), 0);
}

/// write_tx bumps tx_id in its own snapshot before any commit.
#[test]
fn write_tx_handle_has_incremented_tx_id() {
    let mgr = make_manager(8);
    let wtx = mgr.write_tx();
    assert_eq!(wtx.superblock.tx_id.get(), 1);
}

/// commit(None) must advance the manager's current tx_id.
#[test]
fn commit_none_advances_current_tx_id() {
    let mgr = make_manager(8);
    mgr.write_tx().commit(Durability::None).unwrap();
    let rtx = mgr.read_tx();
    assert_eq!(rtx.superblock_snapshot.tx_id.get(), 1);
}

/// Five sequential commits advance tx_id from 0 to 5.
#[test]
fn sequential_commits_advance_tx_id_monotonically() {
    let mgr = make_manager(8);
    for expected in 1u64..=5 {
        mgr.write_tx().commit(Durability::None).unwrap();
        assert_eq!(mgr.read_tx().superblock_snapshot.tx_id.get(), expected);
    }
}

/// alloc_bump_next_id increments with each get_page_alloc call.
#[test]
fn alloc_bump_advances_per_allocation() {
    let mgr = make_manager(16);
    let mut wtx = mgr.write_tx();
    let start = wtx.superblock.alloc_bump_next_id.get();

    drop(wtx.get_page_alloc().unwrap());
    assert_eq!(wtx.superblock.alloc_bump_next_id.get(), start + 1);

    drop(wtx.get_page_alloc().unwrap());
    assert_eq!(wtx.superblock.alloc_bump_next_id.get(), start + 2);
}

/// alloc_bump_next_id is preserved across a commit.
#[test]
fn alloc_bump_persists_after_commit() {
    let mgr = make_manager(16);
    {
        let mut wtx = mgr.write_tx();
        drop(wtx.get_page_alloc().unwrap());
        drop(wtx.get_page_alloc().unwrap());
        wtx.commit(Durability::None).unwrap();
    }
    // next write tx should see alloc_bump = 3 (1 superblock + 2 allocated)
    let wtx2 = mgr.write_tx();
    assert_eq!(wtx2.superblock.alloc_bump_next_id.get(), 3);
}

// -------------------------------------------------------------------------
// Snapshot isolation
// -------------------------------------------------------------------------

/// A read_tx captures the state at the moment it is opened; a subsequent
/// commit must not be visible through the already-open snapshot.
#[test]
fn read_tx_snapshot_is_isolated() {
    let mgr = make_manager(8);

    // open snapshot before any commit
    let rtx = mgr.read_tx();
    let snapshot_tx_id = rtx.superblock_snapshot.tx_id.get();

    // commit a write (use another thread to avoid holding write lock while rtx is open)
    let mgr_ref = &mgr;
    std::thread::scope(|s| {
        s.spawn(|| {
            mgr_ref.write_tx().commit(Durability::None).unwrap();
        });
    });

    // snapshot is frozen at its creation point
    assert_eq!(rtx.superblock_snapshot.tx_id.get(), snapshot_tx_id);

    // drop the old snapshot, then a freshly-opened read_tx sees the new state
    drop(rtx);
    let rtx2 = mgr.read_tx();
    assert_eq!(rtx2.superblock_snapshot.tx_id.get(), snapshot_tx_id + 1);
}

// -------------------------------------------------------------------------
// Multithreaded
// -------------------------------------------------------------------------

/// Many threads can hold simultaneous read_txs without deadlocking.
#[test]
fn concurrent_reads_do_not_deadlock() {
    let mgr = Arc::new(make_manager(16));
    let n = 16usize;
    let barrier = Arc::new(Barrier::new(n));

    let handles: Vec<_> = (0..n)
        .map(|_| {
            let m = Arc::clone(&mgr);
            let b = Arc::clone(&barrier);
            std::thread::spawn(move || {
                let rtx = m.read_tx();
                b.wait(); // all threads hold their read_tx at the same time
                let _ = rtx.superblock_snapshot.tx_id.get();
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}

/// Write transactions must be mutually exclusive: the second writer must not
/// enter its critical section until the first has released the lock.
#[test]
fn write_txs_are_serialized() {
    let mgr = Arc::new(make_manager(8));
    let first_inside = Arc::new(AtomicBool::new(false));
    let first_done = Arc::new(AtomicBool::new(false));

    let m1 = Arc::clone(&mgr);
    let inside1 = Arc::clone(&first_inside);
    let done1 = Arc::clone(&first_done);

    let h1 = std::thread::spawn(move || {
        let _wtx = m1.write_tx();
        inside1.store(true, StdOrdering::Release);
        // hold the lock a little while
        std::thread::sleep(std::time::Duration::from_millis(30));
        done1.store(true, StdOrdering::Release);
        // _wtx dropped here, releasing the lock
    });

    // wait until h1 has the lock
    while !first_inside.load(StdOrdering::Acquire) {
        std::hint::spin_loop();
    }

    let m2 = Arc::clone(&mgr);
    let done2 = Arc::clone(&first_done);
    let h2 = std::thread::spawn(move || {
        // blocks here until h1 releases the lock
        let _wtx = m2.write_tx();
        assert!(
            done2.load(StdOrdering::Acquire),
            "second writer entered before first writer finished"
        );
    });

    h1.join().unwrap();
    h2.join().unwrap();
}

/// Interleaved readers and a writer: readers opened before the commit keep
/// their old snapshot; readers opened after see the new tx_id.
#[test]
fn readers_and_writer_interleave_correctly() {
    // Each read_tx must live on its own thread (re-entrant guard panics).
    let mgr = Arc::new(make_manager(16));

    // Barrier: hold N pre-commit readers open until the commit has happened.
    const N: usize = 4;
    let committed = Arc::new(AtomicBool::new(false));
    let all_open = Arc::new(Barrier::new(N + 1)); // N readers + coordinator

    let pre_handles: Vec<_> = (0..N)
        .map(|_| {
            let m = Arc::clone(&mgr);
            let b = Arc::clone(&all_open);
            let c = Arc::clone(&committed);
            std::thread::spawn(move || {
                let rtx = m.read_tx();
                b.wait(); // signal that we are open
                          // spin until the coordinator has committed
                while !c.load(StdOrdering::Acquire) {
                    std::hint::spin_loop();
                }
                // we must still see tx_id == 0
                assert_eq!(
                    rtx.superblock_snapshot.tx_id.get(),
                    0,
                    "pre-commit reader must see tx_id=0"
                );
            })
        })
        .collect();

    all_open.wait(); // wait for all readers to be open
    mgr.write_tx().commit(Durability::None).unwrap();
    committed.store(true, StdOrdering::Release);

    for h in pre_handles {
        h.join().unwrap();
    }

    // Post-commit readers, each in its own thread.
    let post_handles: Vec<_> = (0..N)
        .map(|_| {
            let m = Arc::clone(&mgr);
            std::thread::spawn(move || {
                let rtx = m.read_tx();
                assert_eq!(
                    rtx.superblock_snapshot.tx_id.get(),
                    1,
                    "post-commit reader must see tx_id=1"
                );
            })
        })
        .collect();
    for h in post_handles {
        h.join().unwrap();
    }
}

/// Multiple threads each run several write+commit cycles; the final tx_id
/// must equal the total number of commits.
#[test]
fn concurrent_sequential_commits_accumulate_tx_id() {
    const THREADS: u64 = 4;
    const COMMITS_PER_THREAD: u64 = 8;

    let mgr = Arc::new(make_manager(32));
    let barrier = Arc::new(Barrier::new(THREADS as usize));

    let handles: Vec<_> = (0..THREADS)
        .map(|_| {
            let m = Arc::clone(&mgr);
            let b = Arc::clone(&barrier);
            std::thread::spawn(move || {
                b.wait(); // start all threads simultaneously
                for _ in 0..COMMITS_PER_THREAD {
                    m.write_tx().commit(Durability::None).unwrap();
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    let final_tx_id = mgr.read_tx().superblock_snapshot.tx_id.get();
    assert_eq!(final_tx_id, THREADS * COMMITS_PER_THREAD);
}
*/
