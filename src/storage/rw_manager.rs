use std::sync::Arc;

use parking_lot::Mutex;
use parking_lot::MutexGuard;
use parking_lot::RwLock;

use super::page_buffer::frame::FrameReadGuard;
use super::page_buffer::frame::FrameWriteGuard;
use super::page_buffer::io::IOFactory;
use super::page_buffer::PageBuffer;
use super::pages::SuperblockHeader;
use super::pages::SuperblockPage;

/// Copy-on-Write storage-engine manager
pub(crate) struct TxManager {
    page_buffer: PageBuffer,
    current: RwLock<SuperblockHeader>,
    write_lock: Mutex<()>,
}

#[derive(Clone, Copy)]
struct Curr {
    superblock_page_id: u64,
    next_page_id: u64,
    tx_id: u64,
}

impl TxManager {
    /// Initializes a new database - NOTE Destructive!
    pub(crate) fn new(io: Arc<dyn IOFactory>, frame_count: usize, page_size: u16) -> Self {
        let superblock_page_id = 0;
        let tx_id = 0;
        let next_page_id = 1;

        let page_buffer = PageBuffer::new(io, frame_count);
        // initialize our first superblock page - the frame will be set to dirty on drop
        let page_header = SuperblockPage::new_with_buffer(
            page_buffer.get_page_new(superblock_page_id).buffer,
            page_size,
            superblock_page_id,
            tx_id,
            next_page_id,
        )
        .clone_header();

        let mgr = TxManager { page_buffer, current: RwLock::new(page_header), write_lock: Mutex::new(()) };

        mgr
    }

    pub(crate) fn read_tx<'tx>(&'tx self) -> ReadTxHandle<'tx> {
        let current = {
            // we need to hold this guard while we put our value in the registry
            let curr_guard = self.current.read();
            let current = curr_guard.clone_header();

            let tx_id = current.tx_id.get();
            tracing::debug!("read_tx opened with tx_id={}", tx_id);
            thread_local_tx_registry::register(tx_id);

            current
        };

        ReadTxHandle { mgr: self, superblock_snapshot: current }
    }

    pub(crate) fn write_tx<'tx>(&'tx self) -> WriteTxHandle<'tx> {
        let lock = self.write_lock.lock();

        let mut new_header = self.current.read().clone_header();
        new_header.tx_id += 1;

        tracing::debug!("write_tx opened with tx_id={}", new_header.tx_id);

        WriteTxHandle { mgr: self, lock, superblock: new_header }
    }
}

pub(crate) trait PageReader {
    fn get_page_read(&self, page_id: u64) -> Result<FrameReadGuard<'_>, std::io::ErrorKind>;
}

pub(crate) trait PageWriter {
    fn get_page_alloc(&mut self) -> FrameWriteGuard<'_>;
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

impl PageReader for ReadTxHandle<'_> {
    fn get_page_read(&self, page_id: u64) -> Result<FrameReadGuard<'_>, std::io::ErrorKind> {
        self.mgr.page_buffer.get_page_existing(page_id)
    }
}

// --- Write handle ---

pub(crate) struct WriteTxHandle<'tx> {
    mgr: &'tx TxManager,
    lock: MutexGuard<'tx, ()>,
    /// Holds this WriteTx's tx_id as well as its new assigned superblock_page_id
    pub(crate) superblock: SuperblockHeader,
}

// TODO this needs to write superblock as well
impl Drop for WriteTxHandle<'_> {
    fn drop(&mut self) {
        *self.mgr.current.write() = self.superblock.clone_header();
    }
}

// TODO to abort transaction dropping the transaction handle should be sufficient, as long as we
// only write-out pages at the end (keep track of touched pages and mark as dirty at commit)
// actually if we write out pages early it doesnt really matter- they will be "unallocated" once we
// roll back to our previous superblock header

impl PageReader for WriteTxHandle<'_> {
    fn get_page_read(&self, page_id: u64) -> Result<FrameReadGuard<'_>, std::io::ErrorKind> {
        self.mgr.page_buffer.get_page_existing(page_id)
    }
}

impl PageWriter for WriteTxHandle<'_> {
    /// Bump allocates
    fn get_page_alloc(&mut self) -> FrameWriteGuard<'_> {
        let page_id = self.superblock.alloc_bump_next_id.get();
        self.superblock.alloc_bump_next_id += 1;
        self.mgr.page_buffer.get_page_new(page_id)
    }
}

pub(crate) enum Durability {
    None,
    Flush,
    Sync,
}

impl WriteTxHandle<'_> {
    pub(crate) fn commit(mut self, _durability: Durability) {
        // TODO

        // might need to track dierty pages? We can do it with the PageWriter methods
        // not sure
        // this needs to write superblock of course - maybe thats it? + flush all dirty ofc
        // althoug that could be an option

        // finally: swap our active superblock
        std::mem::swap(&mut self.superblock, &mut *self.mgr.current.write());
    }
}

// --- Tx Registry ---

/// Thread-local tx_id reader registry
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
