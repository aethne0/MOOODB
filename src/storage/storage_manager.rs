use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs::File;
use std::ops::AddAssign;
use std::os::unix::fs::FileExt;

use super::compute_checksum;
use super::hash_u64_modulo;
use super::page_superblock::*;
use super::pgid_valid;
use super::serialization::*;
use super::PAGE_SIZE;
use super::PGID_NULL;
use crate::mooo_assert;
use crate::storage::btree::Btree;
use crate::storage::btree::FreelistCursor;
use crate::sync::*;

//  ▄▄▄· ▄▄▄·  ▄▄ • ▄▄▄ .▄▄▄
// ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪▀▄.▀·▀▄ █·
//  ██▀·▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄▐▀▀▄
// ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌▐█•█▌  Page Buffer & IO
// .▀    ▀  ▀ ·▀▀▀▀  ▀▀▀ .▀  ▀

const SHARD_CNT: usize = 256;
const FIRST_TX_ID: u64 = 1;
const NULL_HIGH_TXID: u64 = u64::MAX;

pub(super) struct Pager {
    file:            File,
    frames:          Box<[FrameHeader]>,
    pages:           Box<[FrameBuffer]>,
    // these are Mutexs instead of RwLocks because we often have to take a read-lock, then drop it,
    // then try to take a writelock, then double check - because of sharding it is probably faster
    // to just have it be a mutex
    shard_dirs:      Box<[Mutex<HashMap<u64, usize>>]>,
    eviction_hand:   AtomicUsize,
    tx_id:           AtomicU64,
    curr_superblock: RwLock<SuperblockHeader>,
    write_tx_lock:   Mutex<()>,
}

unsafe impl Sync for Pager {}

impl Pager {
    pub(super) fn new(count: usize, file: File) -> Self {
        let temp_header = SuperblockHeader::new_zeroed();

        let pgr = Self {
            file:            file,
            frames:          (0..count).map(|i| FrameHeader::new(i)).collect(),
            pages:           (0..count).map(|_| FrameBuffer::zeros()).collect(),
            shard_dirs:      (0..SHARD_CNT).map(|_| Mutex::new(HashMap::default())).collect(),
            eviction_hand:   0.into(),
            tx_id:           FIRST_TX_ID.into(),
            write_tx_lock:   Mutex::new(()),
            curr_superblock: RwLock::new(temp_header),
        };

        // page 0&1 are reserved for superblocks
        let superblock_pgid = 0;
        let next_superblock_pgid = superblock_pgid + 1;
        let next_pgid = next_superblock_pgid + 1;

        {
            // write empty second superblock
            let mut whdl = pgr
                .get_frame_write_pgid(next_superblock_pgid)
                .expect("io error on superblock initialization");
            whdl.buf.fill(0);
            whdl.mark_dirty(0);
            pgr.io_write(&mut whdl, next_superblock_pgid)
                .expect("io error on superblock initialization");
        }

        let header = {
            // write actua first superblock
            let mut whdl = pgr
                .get_frame_write_pgid(superblock_pgid)
                .expect("io error on superblock initialization");

            let superblock_header = SuperblockHeader {
                prefix:               PagePrefix::new(superblock_pgid, 0, FIRST_TX_ID),
                version:              SerializedU64(*b"ver:0001"),
                alloc_free_head_pgid: PGID_NULL.into(),
                alloc_bump_next_pgid: next_pgid.into(),
                catalog_head_pgid:    PGID_NULL.into(),
                page_size:            (PAGE_SIZE as u16).into(),
            };

            copy_superblock_to_page(whdl.buf, &superblock_header);
            whdl.mark_dirty(FIRST_TX_ID);
            pgr.io_write(&mut whdl, superblock_pgid)
                .expect("io error on superblock initialization");
            superblock_header
        };

        pgr.file.sync_all().expect("io error on superblock initialization");

        pgr.curr_superblock.write().unwrap().clone_from(&header);
        pgr
    }

    // ------------ frame --------------------------------------------------------------------------

    #[must_use = "RAII WrHdl releases when dropped"]
    fn try_pin_write(&self, index: usize) -> Option<WrHdl<'_>> {
        let frame = &self.frames[index];
        match frame.pins.compare_exchange(0, -1, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => {
                frame.usage.fetch_add(1, Ordering::Relaxed);
                Some(unsafe {
                    WrHdl::from_pager_index(self, index, self.tx_id.load(Ordering::Relaxed))
                })
            }
            Err(_) => None,
        }
    }

    #[must_use = "RAII WrHdl releases when dropped"]
    fn pin_write(&self, index: usize) -> WrHdl<'_> {
        let frame = &self.frames[index];
        let cas_res = frame.pins.compare_exchange(0, -1, Ordering::AcqRel, Ordering::Acquire);
        mooo_assert!(
            cas_res.is_ok(),
            "pin_write should be uncontested (frame_index: {}, cas was: {})",
            index,
            cas_res.unwrap_err()
        );
        frame.usage.fetch_add(1, Ordering::Relaxed);
        unsafe { WrHdl::from_pager_index(self, index, self.tx_id.load(Ordering::Relaxed)) }
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn try_pin_read(&self, index: usize, expected_pgid: u64) -> Option<RdHdl<'_>> {
        let frame = &self.frames[index];

        if *frame.pgid.read().unwrap() != expected_pgid {
            // This was evicted between the time we got it from the dir and the time we got a
            // read-lock - caller will have to retry
            return None;
        }

        // Try to increment the pin counter, as long as its not write locked (-1)
        // successful increment -> Increment usage and return hdl
        // write locked         -> None
        match frame.pins.try_update(Ordering::Release, Ordering::Acquire, |prev| {
            if prev >= 0 {
                Some(prev + 1)
            } else {
                None
            }
        }) {
            Ok(_) => {
                frame.usage.fetch_add(1, Ordering::Relaxed);
                Some(unsafe { RdHdl::from_pager_index(self, index) })
            }
            Err(_) => None,
        }
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn pin_downgrade(&self, whdl: WrHdl<'_>) -> RdHdl<'_> {
        let index = whdl.frame.index;
        std::mem::forget(whdl);

        let frame = &self.frames[index];
        let cas_res = frame.pins.compare_exchange(-1, 1, Ordering::AcqRel, Ordering::Acquire);

        mooo_assert!(cas_res.is_ok(), "pin_downgrade should be uncontested");
        unsafe { RdHdl::from_pager_index(self, index) }
    }

    // ------------ io -----------------------------------------------------------------------------

    /// Note: `pgid` must be set on `whdl`! We use that to know which page to read!
    /// We pass in pgid because we don't want this method to try to take a readlock on the frame's
    /// pgid field, its easier to just manage that in the caller.
    #[must_use = "must handle error"]
    fn io_write(&self, whdl: &mut WrHdl<'_>, pgid: u64) -> Result<(), PagerErr> {
        mooo_assert!(
            whdl.frame.state.load(Ordering::Acquire) == FRAME_DIRTY,
            "should not be calling io_write on non-dirty frame"
        );

        match self
            .file
            .write_at(whdl.buf, pgid * PAGE_SIZE as u64)
            .map(|_| {})
            .map_err(|e| PagerErr::Io(e.kind()))
        {
            Ok(_) => {
                whdl.frame.state.store(FRAME_EVICTABLE, Ordering::Release);
                Ok(())
            }
            Err(err) => Err(err),
        }
    }

    #[must_use = "must handle error"]
    fn io_read(&self, whdl: &mut WrHdl<'_>, pgid: u64) -> Result<(), PagerErr> {
        mooo_assert!(pgid_valid(pgid));

        self.file
            .read_exact_at(whdl.buf, pgid * PAGE_SIZE as u64)
            .map_err(|e| PagerErr::Io(e.kind()))?;

        let checksum = compute_checksum(&whdl.buf[CHECKSUM_START_OFFSET..]);
        let header = PagePrefix::mut_from_prefix(whdl.buf);
        let ok_checksum = header.checksum.get() == checksum;
        let ok_pgid = header.pgid.get() == pgid;
        if !ok_checksum || !ok_pgid {
            return Err(PagerErr::Integrity);
        }

        Ok(())
    }

    #[must_use = "must handle error"]
    fn fsync(&self) -> Result<(), PagerErr> {
        self.file.sync_all().map_err(|err| PagerErr::Io(err.kind()))
    }

    // ------------ pages --------------------------------------------------------------------------

    #[must_use = "no side effects"]
    fn scan_for_eviction_candidate(&self) -> usize {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            if checked_count == self.frames.len() {
                std::hint::spin_loop();
                checked_count = 0;
            }
            checked_count += 1;

            let frame_idx = self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.frames.len();
            let frame = &self.frames[frame_idx];

            if frame.state.load(Ordering::Acquire) == FRAME_IN_TX {
                continue;
            }

            // This could be Relaxed (maybe) but it might result in more aborts once we take the
            // lock later? Would need testing really. Either is "correct" because we recheck later.
            if frame.pins.load(Ordering::Acquire) == 0 {
                let frame_usage_ctr = frame
                    .usage
                    .try_update(Ordering::Relaxed, Ordering::Relaxed, |old| {
                        Some(old.saturating_sub(1))
                    })
                    .unwrap();

                if frame_usage_ctr == 0 {
                    return frame_idx;
                }
            }
        }
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn get_frame_read_pgid(&self, pgid: u64) -> Result<RdHdl<'_>, PagerErr> {
        mooo_assert!(pgid_valid(pgid));
        loop {
            let mut dir = self.shard_dirs[hash_u64_modulo(pgid, SHARD_CNT)].lock().unwrap();

            match dir.get(&pgid) {
                Some(&frame_index) => match self.try_pin_read(frame_index, pgid) {
                    None => {
                        // we got a stale frame - retry
                        continue;
                    }
                    Some(rhdl) => {
                        return Ok(rhdl);
                    }
                },
                None => {
                    // eviction path - these comments apply to `get_page_write` as well
                    let mut whdl = loop {
                        let free_frame_index = self.scan_for_eviction_candidate();
                        match self.try_pin_write(free_frame_index) {
                            None => continue,
                            Some(whdl) => {
                                break whdl;
                            }
                        }
                    };

                    // this can be contested, because someone may have found this frame in the dir,
                    // and is calling `pin_read` and checking the pgid
                    let mut frame_pgid_guard = whdl.frame.pgid.write().unwrap();
                    let frame_pgid = std::mem::replace(&mut *frame_pgid_guard, pgid);

                    // TODO we should drop this and retake it - we are spinning looking for an
                    // eviction candidate while holding the lock
                    // (It is "correct" for now though)
                    dir.insert(pgid, whdl.frame.index);
                    drop(dir);

                    // frame is dirty so we have to write out
                    // we do this while the frame is still in the old dir, because if we remove it
                    // before hand the following race can happen
                    //
                    // 1. we (thread A) remove it from dir
                    // 2. thread B wants the page, looks in dir, doesnt find it
                    // 3. thread B tries to load off disk
                    // -> We havent written it out yet though, so theyll load non-existent/stale data.
                    //
                    // We need thread B to wait on our loading lock instead, and then see the frame
                    // has been evicted, and THEN load it in (because well then have written it out)
                    if whdl.frame.state.load(Ordering::Acquire) == FRAME_DIRTY {
                        self.io_write(&mut whdl, pgid)?;
                    }

                    // remove from old dir if needed
                    // It is ok if threads find this page before we do this, because we are holding
                    // the loading lock, and once we release it they will see the new (to them
                    // unexpected) pgid and they'll retry
                    let mut old_dir =
                        self.shard_dirs[hash_u64_modulo(frame_pgid, SHARD_CNT)].lock().unwrap();
                    old_dir.remove(&frame_pgid);
                    drop(old_dir);

                    self.io_read(&mut whdl, pgid)?;

                    let rhdl = self.pin_downgrade(whdl);
                    drop(frame_pgid_guard);
                    return Ok(rhdl);
                }
            }
        }
    }

    /// Gets an exclusive WHdl to a frame with `pgid`.
    /// Note: this method will initialize the `WHdl`'s `pgid` field
    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_frame_write_pgid(&self, pgid: u64) -> Result<WrHdl<'_>, PagerErr> {
        mooo_assert!(pgid_valid(pgid));
        let mut dir = self.shard_dirs[hash_u64_modulo(pgid, SHARD_CNT)].lock().unwrap();

        match dir.get(&pgid) {
            Some(&frame_index) => {
                let whdl = self.pin_write(frame_index);
                whdl.frame.state.store(FRAME_IN_TX, Ordering::Release);
                return Ok(whdl);
            }
            None => {
                let mut whdl = loop {
                    let free_frame_index = self.scan_for_eviction_candidate();
                    match self.try_pin_write(free_frame_index) {
                        None => continue,
                        Some(whdl) => {
                            break whdl;
                        }
                    }
                };

                let mut loading_guard = whdl.frame.pgid.write().unwrap();
                let frame_old_pgid = std::mem::replace(&mut *loading_guard, pgid);
                // we do this here but not `get_frame_write_index` because `get_frame_write_index`
                // should only be called on frames/pages already "created" by our tx.
                whdl.frame.state.store(FRAME_IN_TX, Ordering::Release);

                dir.insert(pgid, whdl.frame.index);
                drop(dir);

                if whdl.frame.state.load(Ordering::Acquire) == FRAME_DIRTY {
                    self.io_write(&mut whdl, frame_old_pgid)?;
                }

                let mut old_dir =
                    self.shard_dirs[hash_u64_modulo(frame_old_pgid, SHARD_CNT)].lock().unwrap();
                old_dir.remove(&frame_old_pgid);
                drop(old_dir);

                return Ok(whdl);
            }
        };
    }

    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_frame_write_index(&self, frame_index: usize) -> WrHdl<'_> {
        let whdl = self.try_pin_write(frame_index).expect("must be uncontested");
        whdl
    }

    #[must_use = "RAII ReadTxHdl releases when dropped"]
    pub(crate) fn read_tx<'tx>(&'tx self) -> ReadTx<'tx> {
        let superblock = {
            // we need to hold this guard while we put our value in the registry
            let curr_guard = self.curr_superblock.read().expect("todo");
            let current = curr_guard.clone();

            let txid = current.txid.get();
            read_tx_registry::register(txid);

            current
        };

        ReadTx { pager: self, superblock }
    }

    #[must_use = "RAII WriteTxHdl releases when dropped"]
    pub(crate) fn write_tx<'tx>(&'tx self) -> WriteTx<'tx> {
        let lock = self.write_tx_lock.lock().unwrap();

        let mut superblock = self.curr_superblock.read().expect("todo").clone();
        let prev_pgid = superblock.pgid.get();
        superblock.txid += 1;
        superblock.pgid.set((prev_pgid + 1) % 2);

        let read_tx = {
            let superblock = superblock.clone();
            read_tx_registry::register(superblock.txid.get());
            ReadTx { pager: self, superblock }
        };

        let freelist_crs = match superblock.alloc_free_head_pgid.get() {
            PGID_NULL => None,
            freelist_pgid => Some(FreelistCursor::new(&read_tx, freelist_pgid).expect("todo")),
        };

        WriteTx {
            read_tx: read_tx,
            pager: self,
            superblock: superblock,
            written_pages: HashMap::new(),
            freed_pages: vec![],
            unfreed_pages: vec![],
            _writer_tx_lock: lock,
            freelist_crs,
        }
    }
}

// ------------ Frame Definitions ------------------------------------------------------------------

#[repr(align(4096))]
struct FrameBuffer(UnsafeCell<[u8; PAGE_SIZE]>);

impl FrameBuffer {
    #[must_use]
    fn zeros() -> Self {
        Self(UnsafeCell::new([0; PAGE_SIZE]))
    }
}

const FRAME_EVICTABLE: u64 = 0;
const FRAME_IN_TX: u64 = 1;
const FRAME_DIRTY: u64 = 2;

// #[repr(align(64))]
struct FrameHeader {
    index: usize,
    /// Negative is write, positive is read - write is exclusive
    pins:  AtomicI64,
    usage: AtomicU64,
    state: AtomicU64,
    /// This doubles as a loading barrier - threads that want to read this page will attempt to take
    /// a readlock on this field, and writers will take a writelock, therefore readers will block
    /// until a reader has atomically (re-)populated the page and updated inner pgid.
    ///
    /// PERF the stdlib implementation of this does a CMPXCHG every single time we add a reader,
    /// which means cache invalidation - this likely could be more optimized using a custom lock but
    /// its not worthwhile because were already incrementing pin+usage which reside in the same
    /// cacheline.
    pgid:  RwLock<u64>,
}

impl FrameHeader {
    fn new(index: usize) -> Self {
        Self {
            index: index,
            pins:  0.into(),
            usage: 0.into(),
            state: 0.into(),
            pgid:  RwLock::new(PGID_NULL),
        }
    }
}

// ------------ WrHdl ------------------------------------------------------------------------------

/// Exclusive frame write-handle
pub(super) struct WrHdl<'pager> {
    pub(super) buf: &'pager mut [u8; PAGE_SIZE],
    pager:          &'pager Pager,
    frame:          &'pager FrameHeader,
    txid:           u64,
    dirty:          bool,
}

impl<'pager> WrHdl<'pager> {
    unsafe fn from_pager_index(pager: &'pager Pager, index: usize, txid: u64) -> Self {
        let frame = &pager.frames[index];
        let buf = unsafe { &mut *pager.pages[index].0.get() };
        Self { pager: pager, frame: frame, buf: buf, txid, dirty: false }
    }

    pub(super) fn get_pgid(&self) -> u64 {
        let pgid = *self.frame.pgid.read().unwrap();
        mooo_assert!(pgid_valid(pgid));
        pgid
    }

    pub(super) fn get_frame_index(&self) -> usize {
        self.frame.index
    }

    /// Sets checksum and pgid on the page header prefix and marks the frame as dirty
    /// NOTE This should only be done once! We will panic if we call this on a dirty frame
    /// NOTE This must be called even if immediately before a write-out, because we set the header
    /// fields with it
    fn mark_dirty(&mut self, txid: u64) {
        let pgid = self.get_pgid();
        mooo_assert!(pgid_valid(pgid));
        mooo_assert!(txid != NULL_HIGH_TXID);

        let prev_frame_state = self.frame.state.swap(FRAME_DIRTY, Ordering::AcqRel);
        mooo_assert!(prev_frame_state == FRAME_IN_TX);

        let header = PagePrefix::mut_from_prefix(self.buf);
        header.pgid.set(pgid);
        header.txid.set(txid);

        // Checksum must computed after other sets!
        let checksum = compute_checksum(&self.buf[CHECKSUM_START_OFFSET..]);
        let header = PagePrefix::mut_from_prefix(self.buf);
        header.checksum.set(checksum);
    }
}

impl Drop for WrHdl<'_> {
    fn drop(&mut self) {
        let prev = self.pager.frames[self.frame.index].pins.fetch_add(1, Ordering::AcqRel);
        mooo_assert!(prev == -1, "write-pin should have been -1");
    }
}

// ------------ RdHdl ------------------------------------------------------------------------------

/// Shared frame read-handle
pub(super) struct RdHdl<'pager> {
    pub(super) buf: &'pager [u8; PAGE_SIZE],
    pager:          &'pager Pager,
    frame:          &'pager FrameHeader,
}

impl<'pager> RdHdl<'pager> {
    unsafe fn from_pager_index(pager: &'pager Pager, index: usize) -> Self {
        let frame = &pager.frames[index];
        let buf = unsafe { &*pager.pages[index].0.get() };
        Self { pager: pager, frame: frame, buf: buf }
    }
}

impl Drop for RdHdl<'_> {
    fn drop(&mut self) {
        let prev = self.pager.frames[self.frame.index].pins.fetch_sub(1, Ordering::Release);
        mooo_assert!(prev > 0, "read-pin should have been 1 or greater");
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PagerErr {
    Io(std::io::ErrorKind),
    /// `page_id` or `checksum` did not match
    Integrity,
}

// ▄▄▄▄▄▐▄• ▄
// •██   █▌█▌▪
//  ▐█.▪ ·██·
//  ▐█▌·▪▐█·█▌  WriteTx & ReadTx
//  ▀▀▀ •▀▀ ▀▀

// ------------ Thread-Local Read-tx Registry ------------------------------------------------------

mod read_tx_registry {
    use super::NULL_HIGH_TXID;
    use crate::mooo_assert;
    use crate::sync::*;

    const MAX_THREADS: usize = 256;
    static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
    fn get_next_thread_local_index() -> usize {
        let next = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        mooo_assert!(next < MAX_THREADS);
        next
    }

    // possibly these should be spaced out for a cache-line each
    static COUNTERS: [AtomicU64; MAX_THREADS] =
        [const { AtomicU64::new(NULL_HIGH_TXID) }; MAX_THREADS];
    thread_local! {
        static THREAD_INDEX: usize = get_next_thread_local_index();
    }

    pub(super) fn register(tx_id: u64) {
        mooo_assert!(tx_id != NULL_HIGH_TXID);
        THREAD_INDEX.with(|&thread_index| {
            COUNTERS[thread_index]
                .compare_exchange(NULL_HIGH_TXID, tx_id, Ordering::Release, Ordering::Relaxed)
                .expect("tried to take re-entrant read guard");
        });
    }
    pub(super) fn deregister() {
        THREAD_INDEX.with(|&thread_index| {
            COUNTERS[thread_index].store(NULL_HIGH_TXID, Ordering::Release);
        });
    }

    pub(super) fn get_min() -> u64 {
        // its ok if our max index gets stale, because the new thread we didnt see will definitely
        // have a tx_id GE to any of these
        let count = NEXT_ID.load(Ordering::Relaxed);
        let mut earliest = NULL_HIGH_TXID;
        for i in 0..count {
            earliest = earliest.min(COUNTERS[i].load(Ordering::Acquire));
        }
        earliest
    }
}

// ------------ ReadTx -----------------------------------------------------------------------------

pub(super) trait PageReader<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr>;
}

pub(super) struct ReadTx<'tx> {
    pager:      &'tx Pager,
    superblock: SuperblockHeader,
}

impl Drop for ReadTx<'_> {
    fn drop(&mut self) {
        read_tx_registry::deregister();
    }
}

impl ReadTx<'_> {
    pub(super) fn get_catalog_root_pgid(&self) -> u64 {
        self.superblock.catalog_head_pgid.get()
    }
}

impl<'tx> PageReader<'tx> for ReadTx<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_frame_read_pgid(pgid)
    }
}

// ------------ WriteTx ----------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub(super) enum Durability {
    /// New pages will reside in the page buffer and be marked them as dirty, but no IO operations
    /// will be done - they will be lazily written out by evictions or by explicit flush calls
    Lazy,
    /// Writes (IO) to disk but does not fsync
    Flush,
    /// Writes and fsyncs
    Sync,
}

pub(super) trait PageWriter<'tx> {
    /// This will give a writeable page from a requested `pgid`, which can mean one of two things
    /// - This `pgid` is from a prev tx, in which case we will copy `pgid`'s frame's contents
    ///    to a new page, and return that new page
    /// - This `pgid` is from the current tx, in which case well return that `pgid`'s frame
    ///
    /// This method should also handle page freeing - in the former case, when an old page is
    /// copied, that old page should be added to any sort of free-list that the implementor
    /// maintains. This part is optional and up to the implementor - endlessly bump-allocating and
    /// "leaking" pages is "correct".
    ///
    /// Note: it is the implementors job to set the `pgid` of this handed our WrHdl
    fn get_page_write<'op>(&'op mut self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr>;
    fn get_page_alloc<'op>(&'op mut self) -> Result<WrHdl<'tx>, PagerErr>;
    fn free_page(&mut self, pgid: u64);
}

/// A write-tx that uses bump-allocation only
pub(super) struct WriteTx<'tx> {
    read_tx:         ReadTx<'tx>,
    pager:           &'tx Pager,
    superblock:      SuperblockHeader,
    written_pages:   HashMap<u64, usize>,
    freed_pages:     Vec<u64>,
    unfreed_pages:   Vec<FreeEntry>,
    _writer_tx_lock: MutexGuard<'tx, ()>,
    freelist_crs:    Option<FreelistCursor<'tx>>, // Hmm...
}

impl<'tx> WriteTx<'tx> {
    pub(super) fn get_catalog_root_pgid(&self) -> u64 {
        self.superblock.catalog_head_pgid.get()
    }

    pub(super) fn set_catalog_root_pgid(&mut self, pgid: u64) {
        self.superblock.catalog_head_pgid.set(pgid);
    }

    pub(super) fn commit(mut self, durability: Durability) -> Result<(), PagerErr> {
        let should_write = matches!(durability, Durability::Sync | Durability::Flush);
        let should_fsync = matches!(durability, Durability::Sync);

        // write freed pages to freelist, repeatedly until we converge on 0 freed pages
        if self.freed_pages.len() > 0 || self.unfreed_pages.len() > 0 {
            let old_freelist_pgid = self.superblock.alloc_free_head_pgid.get();
            let txid = self.superblock.txid.get();

            let mut freelist = if old_freelist_pgid != PGID_NULL {
                self.freed_pages.push(old_freelist_pgid);
                Btree::new_from_root_pgid(old_freelist_pgid)
            } else {
                Btree::new(&mut self.bump_allocator())?
            };

            loop {
                let mut cont = false;

                if let Some(free_entry) = self.unfreed_pages.pop() {
                    freelist.delete(&mut self.freelist_allocator()?, free_entry.as_bytes())?;
                    cont = true;
                };

                if let Some(pgid) = self.freed_pages.pop() {
                    freelist.insert(
                        &mut self.freelist_allocator()?,
                        FreeEntry::new(txid, pgid).as_bytes(),
                        pgid,
                    )?;
                    cont = true;
                };

                if !cont {
                    break;
                }
            }

            self.superblock.alloc_free_head_pgid = freelist.get_root_pgid().into();
        }

        // write "created" pages (written to pages)
        for &frame_index in self.written_pages.values() {
            let mut whdl = self.pager.get_frame_write_index(frame_index);
            whdl.mark_dirty(self.superblock.txid.get());
            if should_write {
                let pgid = whdl.get_pgid();
                self.pager.io_write(&mut whdl, pgid)?;
            }
        }

        // update superblock
        let sb_pgid = self.superblock.pgid.get();
        let mut whdl = self.pager.get_frame_write_pgid(sb_pgid)?;
        copy_superblock_to_page(whdl.buf, &self.superblock);

        whdl.mark_dirty(self.superblock.txid.get());
        if should_write {
            let pgid = whdl.get_pgid();
            self.pager.io_write(&mut whdl, pgid)?;
        }

        if should_fsync {
            self.pager.fsync()?;
        }

        // TODO txid should be set long befre this because pin methods use it maybe?
        self.pager.tx_id.store(self.superblock.txid.get(), Ordering::Relaxed);
        *self.pager.curr_superblock.write().unwrap() = self.superblock.clone();

        Ok(())
    }

    /// Page allocator that just bump allocates, only will allocate by incrementing the superblock's
    /// `alloc_bump_next_pgid`.
    ///
    /// Allocators are basically free to construct and can be recursively contrstructed - they hold
    /// no state themselves
    fn bump_allocator<'alloc>(&'alloc mut self) -> BumpAlloc<'alloc, 'tx> {
        BumpAlloc { tx: self }
    }

    /// Page allocator that will try to use the freelist, if its populated, and if there are pages
    /// that are no longer being relied-on by live read-txs, and then fall back to bump allocating.
    ///
    /// Allocators are basically free to construct and can be recursively contrstructed - they hold
    /// no state themselves
    pub(super) fn freelist_allocator<'alloc>(
        &'alloc mut self,
    ) -> Result<FreelistAlloc<'alloc, 'tx>, PagerErr> {
        Ok(FreelistAlloc { tx: self })
    }
}

// ------------ Bump Allocator ---------------------------------------------------------------------

pub(super) struct BumpAlloc<'alloc, 'tx: 'alloc> {
    tx: &'alloc mut WriteTx<'tx>,
}

impl<'alloc, 'tx: 'alloc> PageReader<'tx> for BumpAlloc<'alloc, 'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.tx.pager.get_frame_read_pgid(pgid)
    }
}

impl<'alloc, 'tx: 'alloc> PageWriter<'tx> for BumpAlloc<'alloc, 'tx> {
    fn free_page(&mut self, pgid: u64) {
        self.tx.freed_pages.push(pgid);
    }

    /// Bump allocates - also adds page to our dirty-page linked list
    fn get_page_alloc<'op>(&'op mut self) -> Result<WrHdl<'tx>, PagerErr> {
        let pgid = self.tx.superblock.alloc_bump_next_pgid.get();
        self.tx.superblock.alloc_bump_next_pgid.add_assign(1);
        let whdl = self.tx.pager.get_frame_write_pgid(pgid)?;
        self.tx.written_pages.insert(pgid, whdl.get_frame_index());
        Ok(whdl)
    }

    /// should return a writeable new page, or a writeable copy of an existing page (depending on
    /// pgid)
    fn get_page_write<'op>(&'op mut self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(&index) = self.tx.written_pages.get(&pgid) {
            // this is already a new page per our writetx
            return Ok(self.tx.pager.get_frame_write_index(index));
        }

        // we need to Copy-on-Write
        let old_rhdl = self.get_page_read(pgid)?;
        let new_whdl = self.get_page_alloc()?;
        new_whdl.buf.copy_from_slice(old_rhdl.buf);
        self.free_page(pgid);

        Ok(new_whdl)
    }
}

// ------------ Freelist Allocator -----------------------------------------------------------------

pub(super) struct FreelistAlloc<'alloc, 'tx: 'alloc> {
    tx: &'alloc mut WriteTx<'tx>,
}

impl<'alloc, 'tx: 'alloc> PageReader<'tx> for FreelistAlloc<'alloc, 'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.tx.pager.get_frame_read_pgid(pgid)
    }
}

impl<'alloc, 'tx: 'alloc> PageWriter<'tx> for FreelistAlloc<'alloc, 'tx> {
    fn free_page(&mut self, pgid: u64) {
        // freed pages are only inserted into the freelist at the end
        self.tx.freed_pages.push(pgid);
    }

    /// Freelist allocates - also adds page to our dirty-page linked list
    fn get_page_alloc<'op>(&'op mut self) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(freelist_crs) = &mut self.tx.freelist_crs {
            let free_entry_opt = freelist_crs.next(&self.tx.read_tx)?;
            if let Some(free_entry) = free_entry_opt {
                if free_entry.txid.get() < read_tx_registry::get_min() {
                    self.tx.unfreed_pages.push(free_entry);
                    let pgid = free_entry.pgid.get();
                    let whdl = self.tx.pager.get_frame_write_pgid(pgid)?;
                    self.tx.written_pages.insert(pgid, whdl.get_frame_index());
                    return Ok(whdl);
                }
            }
            // if we didnt return it means we have no more free-able pages
            // well do this so we dont waste time checking again
            self.tx.freelist_crs = None;
        }

        let pgid = self.tx.superblock.alloc_bump_next_pgid.get();
        self.tx.superblock.alloc_bump_next_pgid.add_assign(1);
        let whdl = self.tx.pager.get_frame_write_pgid(pgid)?;
        self.tx.written_pages.insert(pgid, whdl.get_frame_index());
        Ok(whdl)
    }

    /// should return a writeable new page, or a writeable copy of an existing page (depending on
    /// pgid)
    fn get_page_write<'op>(&'op mut self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(&index) = self.tx.written_pages.get(&pgid) {
            // this is already a new page per our writetx
            return Ok(self.tx.pager.get_frame_write_index(index));
        }

        // we need to Copy-on-Write
        let old_rhdl = self.get_page_read(pgid)?;
        let new_whdl = self.get_page_alloc()?;
        new_whdl.buf.copy_from_slice(old_rhdl.buf);
        self.free_page(pgid);

        Ok(new_whdl)
    }
}
