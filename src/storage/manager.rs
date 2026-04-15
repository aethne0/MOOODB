//! manager.rs
//!
//! Manages low level write/read-txs and also acts as a bump allocator

use std::ops::AddAssign;

use rustc_hash::FxHashMap;
use zerocopy::IntoBytes;

use super::frame::FrameReadGuard;
use super::frame::FrameWriteGuard;
use super::frame::Writeable;
use super::pager::Pager;
use super::pages::SuperblockHeader;
use super::pages::SuperblockPage;
use crate::storage::StorageError;
use crate::storage::PAGE_SIZE_U16;
use crate::sync::*;

pub(crate) struct TxManager {
    pager:      Pager,
    current:    RwLock<SuperblockHeader>,
    write_lock: Mutex<()>,
}

#[derive(Clone, Copy)]
struct Curr {
    superblock_page_id: u64,
    next_page_id:       u64,
    tx_id:              u64,
}

impl TxManager {
    /// Initializes a new database - NOTE Destructive!
    pub(crate) fn new(frame_count: usize, file: std::fs::File) -> Self {
        let superblock_page_id = 0;
        let tx_id = 0;
        // page 0&1 are reserved for superblocks
        let next_page_id = 2;

        let pager = Pager::new(frame_count, file);
        // initialize our first superblock page - the frame will be set to dirty on drop
        let page_header = SuperblockPage::new_with_buffer(
            pager
                .get_page_new(superblock_page_id)
                .expect("io error on superblock initialization")
                .buffer(),
            PAGE_SIZE_U16,
            superblock_page_id,
            tx_id,
            next_page_id,
        )
        .clone_header();

        let mgr =
            TxManager { pager, current: RwLock::new(page_header), write_lock: Mutex::new(()) };

        mgr
    }

    pub(crate) fn read_tx<'tx>(&'tx self) -> ReadTxHandle<'tx> {
        let current = {
            // we need to hold this guard while we put our value in the registry
            let curr_guard = self.current.read().expect("todo");
            let current = curr_guard.clone_header();

            let tx_id = current.tx_id.get();
            log::debug!("read_tx opened with tx_id={}", tx_id);
            thread_local_tx_registry::register(tx_id);

            current
        };

        ReadTxHandle { mgr: self, superblock_snapshot: current }
    }

    pub(crate) fn write_tx<'tx>(&'tx self) -> WriteTxHandle<'tx> {
        let lock = self.write_lock.lock().unwrap();

        let mut new_header = self.current.read().expect("todo").clone_header();
        new_header.tx_id += 1;

        log::debug!("write_tx opened with tx_id={}", new_header.tx_id);

        WriteTxHandle {
            next_superblock_id: (new_header.page_id.get() + 1) % 2,
            mgr: self,
            lock,
            superblock: new_header,
            created_page_ids: FxHashMap::default(),
        }
    }
}

pub(crate) trait PageReader<'tx> {
    fn get_page_read(&self, page_id: u64) -> Result<FrameReadGuard<'tx>, StorageError>;
}

pub(crate) trait PageAlloc<'tx> {
    fn get_page_alloc(
        &mut self,
    ) -> Result<(&mut FrameWriteGuard<'tx, Writeable>, u64), StorageError>;
    fn get_page_write(
        &mut self, page_id: u64,
    ) -> Result<(&mut FrameWriteGuard<'tx, Writeable>, u64), StorageError>;
}

// --- Read handle ---

pub(crate) struct ReadTxHandle<'tx> {
    mgr: &'tx TxManager,
    pub(crate) superblock_snapshot: SuperblockHeader,
}

impl Drop for ReadTxHandle<'_> {
    fn drop(&mut self) {
        thread_local_tx_registry::deregister();
    }
}

impl<'alloc> PageReader<'alloc> for ReadTxHandle<'alloc> {
    fn get_page_read(&self, page_id: u64) -> Result<FrameReadGuard<'alloc>, StorageError> {
        self.mgr.pager.get_page_existing(page_id)
    }
}

// --- Write handle ---

pub(crate) struct WriteTxHandle<'tx> {
    /// Holds this WriteTx's tx_id as well as its new assigned superblock_page_id
    next_superblock_id:    u64,
    created_page_ids:      FxHashMap<u64, FrameWriteGuard<'tx, Writeable>>,
    mgr:                   &'tx TxManager,
    lock:                  MutexGuard<'tx, ()>,
    pub(crate) superblock: SuperblockHeader,
}

// to abort transaction dropping the transaction handle should be sufficient, as long as we
// only write-out pages at the end (keep track of touched pages and mark as dirty at commit)
// actually if we write out pages early it doesnt really matter- they will be "unallocated" once we
// roll back to our previous superblock header

impl<'tx> PageReader<'tx> for WriteTxHandle<'tx> {
    fn get_page_read(&self, page_id: u64) -> Result<FrameReadGuard<'tx>, StorageError> {
        self.mgr.pager.get_page_existing(page_id)
    }
}

impl<'tx> PageAlloc<'tx> for WriteTxHandle<'tx> {
    /// Bump allocates - also adds page to our dirty-page linked list
    fn get_page_alloc(
        &mut self,
    ) -> Result<(&mut FrameWriteGuard<'tx, Writeable>, u64), StorageError> {
        let page_id = self.superblock.alloc_bump_next_id.get();
        self.superblock.alloc_bump_next_id.add_assign(1);
        let frame = self.mgr.pager.get_page_new(page_id)?;
        self.created_page_ids.insert(page_id, frame);
        let frame_ref = self.created_page_ids.get_mut(&page_id).unwrap();
        Ok((frame_ref, page_id))
    }

    /// should return a writeable new page, or a writeable copy of an existing page (depending on
    /// page_id)
    fn get_page_write(
        &mut self, page_id: u64,
    ) -> Result<(&mut FrameWriteGuard<'tx, Writeable>, u64), StorageError> {
        // rust smh
        if self.created_page_ids.contains_key(&page_id) {
            // if we say `if let Some(xxx) = created_page_ids.get_mut() ...` then well
            // be borrowing created_page_ids for the lifetime of the return, therefore if we
            // dont find some well still be mut borrowing it and can't do the below stuff
            //
            // I think the only way around this is to implement our own HashMap
            return Ok((self.created_page_ids.get_mut(&page_id).unwrap(), page_id));
        }

        let old_frame = self.get_page_read(page_id)?;
        let (new_frame, new_page_id) = self.get_page_alloc()?;

        new_frame.buffer().copy_from_slice(old_frame.buffer());

        Ok((new_frame, new_page_id))
    }
}

pub(crate) enum Durability {
    None,
    Flush,
    Sync,
}

impl<'a> WriteTxHandle<'a> {
    pub(crate) fn commit(self, durability: Durability) -> Result<(), StorageError> {
        if matches!(durability, Durability::Flush | Durability::Sync) {
            // we need to make a real page for our superblock, copy our header, then write
            let mut superblock_frame = self.mgr.pager.get_page_new(self.next_superblock_id)?;
            self.superblock.write_to_prefix(superblock_frame.buffer()).unwrap();
            self.mgr.pager.io_flush_and_resident(superblock_frame.commit())?;

            for page in self.created_page_ids.into_values() {
                self.mgr.pager.io_flush_and_resident(page.commit())?;
            }

            if matches!(durability, Durability::Sync) {
                self.mgr.pager.sync()?;
            }
        }

        // finally: publish our new superblock. Drop will repeat this write, making it idempotent.
        // (swap would leave the old header in self.superblock which Drop would then write back)
        *self.mgr.current.write().unwrap() = self.superblock.clone_header();
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------------
// *            Thread-Local Read-tx Registry                                                      *
// -------------------------------------------------------------------------------------------------

mod thread_local_tx_registry {
    use std::sync::atomic::AtomicU64;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    const MAX_THREADS: usize = 256;
    static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
    fn get_next_thread_local_index() -> usize {
        let next = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        assert!(next < MAX_THREADS);
        next
    }

    // possibly these should be spaced out for a cache-line each
    static COUNTERS: [AtomicU64; MAX_THREADS] = [const { AtomicU64::new(u64::MAX) }; MAX_THREADS];
    thread_local! {
        static THREAD_INDEX: usize = get_next_thread_local_index();
    }

    pub(super) fn register(tx_id: u64) {
        THREAD_INDEX.with(|&thread_index| {
            COUNTERS[thread_index]
                .compare_exchange(u64::MAX, tx_id, Ordering::Release, Ordering::Relaxed)
                .expect("tried to take re-entrant read guard");
        });
    }
    pub(super) fn deregister() {
        THREAD_INDEX.with(|&thread_index| {
            COUNTERS[thread_index].store(u64::MAX, Ordering::Release);
        });
    }

    pub(super) fn get_min() -> u64 {
        // its ok if our max index gets stale, because the new thread we didnt see will definitely have
        // a tx_id GE to any of these
        let count = NEXT_ID.load(Ordering::Relaxed);
        let mut earliest = u64::MAX;
        for i in 0..count {
            earliest = earliest.min(COUNTERS[i].load(Ordering::Acquire));
        }
        earliest
    }
}
