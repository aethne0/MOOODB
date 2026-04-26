// TODO when a transaction fails we have stuck InTx frames

use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs::File;
use std::mem::replace;
use std::ops::AddAssign;
use std::os::unix::fs::FileExt;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::RwLock;

use super::btree::Btree;
use super::compute_checksum;
use super::frame_latch::*;
use super::hash_u64_modulo;
use super::page_superblock::*;
use super::pgid_valid;
use super::serialization::*;
use super::PAGE_SIZE;
use super::PGID_NULL;
use crate::mooo_assert;

//  ▄▄▄· ▄▄▄·  ▄▄ • ▄▄▄ .▄▄▄
// ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪▀▄.▀·▀▄ █·
//  ██▀·▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄▐▀▀▄
// ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌▐█•█▌  Page Buffer & IO
// .▀    ▀  ▀ ·▀▀▀▀  ▀▀▀ .▀  ▀

const ON_DISK_VERSION: u64 = 1;
const SHARD_CNT: usize = 256;
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
    superblock_curr: RwLock<SuperblockHeader>,
    writer_lock:     Mutex<()>,
}

unsafe impl Sync for Pager {}

impl Pager {
    pub(super) fn new(count: usize, file: File) -> Result<Self, PagerErr> {
        let temp_header = SuperblockHeader::new_zeroed();

        let pager = Self {
            file:            file,
            frames:          (0..count).map(|i| FrameHeader::new(i)).collect(),
            pages:           (0..count).map(|_| FrameBuffer::zeros()).collect(),
            shard_dirs:      (0..SHARD_CNT).map(|_| Mutex::new(HashMap::default())).collect(),
            eviction_hand:   0.into(),
            writer_lock:     Mutex::new(()),
            superblock_curr: RwLock::new(temp_header),
        };

        // page 0&1 are reserved for superblocks
        let pgid_superblock = 0;
        let pgid_bump_next = 2;
        let txid_first = 0;

        let header = {
            // write actual first superblock
            let mut whdl = pager.get_frame_write_pgid(pgid_superblock)?;

            let superblock_header = SuperblockHeader {
                prefix:         PagePrefix::new(pgid_superblock, 0, txid_first, PGTYPE_SUPERBLOCK),
                pgid_freelist:  PGID_NULL.into(),
                pgid_bump_next: pgid_bump_next.into(),
                pgid_catalog:   PGID_NULL.into(),
                page_size:      (PAGE_SIZE as u16).into(),
            };

            copy_superblock_to_page(whdl.buf, &superblock_header);
            whdl.mark_dirty(txid_first);
            pager.io_write(&mut whdl, pgid_superblock)?;
            superblock_header
        };

        *pager.superblock_curr.write().unwrap() = header;

        {
            // do one tx to create freelist and second superblock
            let mut tx = pager.write_tx();
            let freelist = Btree::new(&mut tx)?;
            tx.superblock.pgid_freelist = freelist.get_root_pgid().into();
            tx.commit(Durability::Flush)?;
        }

        pager.fsync()?;
        Ok(pager)
    }

    // ------------ frame --------------------------------------------------------------------------

    #[must_use = "RAII WrHdl releases when dropped"]
    fn try_pin_write(&self, index: usize) -> Option<WrHdl<'_>> {
        let frame = &self.frames[index];
        let Some(frame_guard) = frame.latch.try_write() else {
            return None;
        };
        frame.usage.fetch_add(1, Ordering::Relaxed);
        Some(unsafe { WrHdl::from_pager_index(self, index, frame_guard) })
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn try_pin_read(&self, index: usize, pgid: u64) -> Option<RdHdl<'_>> {
        let frame = &self.frames[index];
        let frame_guard = frame.latch.read();

        if frame_guard.pgid != pgid {
            // This was evicted between the time we got it from the dir and the time we got a
            // read-lock - caller will have to retry
            return None;
        }

        frame.usage.fetch_add(1, Ordering::Relaxed);
        Some(unsafe { RdHdl::from_pager_index(self, index, frame_guard) })
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn pin_downgrade<'a>(&'a self, whdl: WrHdl<'a>) -> RdHdl<'a> {
        let index = whdl.frame.index;
        let WrHdl { frame_inner, .. } = whdl;
        unsafe { RdHdl::from_pager_index(self, index, latch_downgrade(frame_inner)) }
    }

    // ------------ io -----------------------------------------------------------------------------

    /// We pass in pgid because we don't want this method to try to take a readlock on the frame's
    /// pgid field, its easier to just manage that in the caller.
    #[must_use = "must handle error"]
    fn io_write(&self, whdl: &mut WrHdl<'_>, pgid: u64) -> Result<(), PagerErr> {
        mooo_assert!(
            whdl.frame_inner.state == FrameState::Dirty,
            "should not be calling io_write on non-dirty frame"
        );

        match self
            .file
            .write_at(whdl.buf, pgid * PAGE_SIZE as u64)
            .map(|_| {})
            .map_err(|e| PagerErr::Io(e.kind()))
        {
            Ok(_) => {
                whdl.frame_inner.state = FrameState::Evictable;
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
        let ok_checksum = header.csum.get() == checksum;
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
    fn scan_for_eviction_candidate(&self) -> WrHdl<'_> {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            if checked_count == self.frames.len() {
                std::hint::spin_loop();
                checked_count = 0;
            }
            checked_count += 1;

            let frame_idx = self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.frames.len();
            let frame = &self.frames[frame_idx];

            let Some(frame_wguard) = frame.latch.try_write() else {
                // someones reading|writing this frame
                continue;
            };

            if frame_wguard.state == FrameState::InTx {
                // frame is part of an in-progress write-tx
                continue;
            }

            let frame_usage_ctr = frame
                .usage
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |old| Some(old.saturating_sub(1)))
                .unwrap();

            if frame_usage_ctr == 0 {
                return unsafe { WrHdl::from_pager_index(self, frame_idx, frame_wguard) };
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
                        // someone took this frame and changed its pgid since we checked the dir, so
                        // we will abandon it and try again
                        continue;
                    }
                    Some(rhdl) => {
                        return Ok(rhdl);
                    }
                },
                None => {
                    // eviction path - these comments apply to `get_page_write` as well
                    let mut whdl = self.scan_for_eviction_candidate();

                    // this can be contested, because someone may have found this frame in the dir,
                    // and is calling `pin_read` and checking the pgid
                    let mut frame_wguard = whdl.frame.latch.write();
                    let frame_pgid = replace(&mut frame_wguard.pgid, pgid);

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
                    if frame_wguard.state == FrameState::Dirty {
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
                    drop(frame_wguard);
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
                let mut whdl = self.try_pin_write(frame_index).expect("should be uncontested");
                mooo_assert!(
                    whdl.get_pgid() == pgid,
                    "frame should have same pgid that it is filed under in the dir"
                );
                whdl.frame_inner.state = FrameState::InTx;
                return Ok(whdl);
            }
            None => {
                let mut whdl = self.scan_for_eviction_candidate();
                let frame_old_pgid = replace(&mut whdl.frame_inner.pgid, pgid);
                whdl.frame_inner.state = FrameState::InTx;

                dir.insert(pgid, whdl.frame.index);
                drop(dir);

                if whdl.frame_inner.state == FrameState::Dirty {
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
            let curr_guard = self.superblock_curr.read().expect("todo");
            let current = curr_guard.clone();

            let txid = current.txid.get();
            tx_registry::register(txid);

            current
        };

        ReadTx { pager: self, superblock }
    }

    #[must_use = "RAII WriteTxHdl releases when dropped"]
    pub(crate) fn write_tx<'tx>(&'tx self) -> WriteTx<'tx> {
        let lock = self.writer_lock.lock().unwrap();

        let mut superblock = self.superblock_curr.read().expect("todo").clone();
        let prev_pgid = superblock.pgid.get();
        superblock.txid += 1;
        superblock.pgid.set((prev_pgid + 1) % 2);
        let freelist_pgid = superblock.pgid_freelist;

        tx_registry::register(superblock.txid.get());

        WriteTx {
            pager:      self,
            superblock: superblock,

            pages_allocated: HashMap::new(),
            pages_freed:     Vec::new(),
            pages_free_used: Vec::new(),

            count_freelist_used: 0,
            pgid_freelist_old:   freelist_pgid.get(),

            _writer_tx_lock: lock,
        }
    }
}

// ------------ Frame Definitions ------------------------------------------------------------------
// #[repr(align(4096))]
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

#[repr(u64)]
#[derive(PartialEq, Eq, Clone, Copy)]
enum FrameState {
    Evictable,
    InTx,
    Dirty,
}

#[repr(align(64))]
struct FrameHeader {
    /// This doubles as a loading barrier - threads that want to read this page will attempt to take
    /// a readlock on this field, and writers will take a writelock, therefore readers will block
    /// until a reader has atomically (re-)populated the page and updated inner pgid.
    ///
    /// PERF the stdlib implementation of this does a CMPXCHG every single time we add a reader,
    /// which means cache invalidation - this likely could be more optimized using a custom lock but
    /// its not worthwhile because were already incrementing pin+usage which reside in the same
    /// cacheline.
    latch: Latch<FrameInner>,
    /// Index of frame in our frame pool
    index: usize,
    /// we cant put usage inside `latch` because non-writers need to increment and decrement it
    usage: AtomicU64,
}

struct FrameInner {
    pgid:  u64,
    state: FrameState,
}

impl FrameHeader {
    fn new(index: usize) -> Self {
        Self {
            index: index,
            latch: Latch::new(FrameInner { pgid: PGID_NULL, state: FrameState::Evictable }),
            usage: 0.into(),
        }
    }
}

// ------------ WrHdl ------------------------------------------------------------------------------

/// Exclusive frame write-handle
pub(super) struct WrHdl<'pager> {
    pager:          &'pager Pager,
    frame:          &'pager FrameHeader,
    frame_inner:    LatchWriteGuard<'pager, FrameInner>,
    pub(super) buf: &'pager mut [u8; PAGE_SIZE],
}

impl<'pager> WrHdl<'pager> {
    /// SAFETY frame_guard must be acquired from frame with index `index`
    unsafe fn from_pager_index(
        pager: &'pager Pager, index: usize, frame_guard: LatchWriteGuard<'pager, FrameInner>,
    ) -> Self {
        let frame = &pager.frames[index];
        // SAFETY as long as the frame_guard has been acquired from this frame (frame with `index`)
        // then we know we effectively have a write-lock on this data
        let buf = unsafe { &mut *pager.pages[index].0.get() };
        Self { frame: frame, frame_inner: frame_guard, pager: pager, buf: buf }
    }

    pub(super) fn get_pgid(&self) -> u64 {
        let pgid = self.frame_inner.pgid;
        mooo_assert!(pgid_valid(pgid));
        pgid
    }

    pub(super) fn get_frame_index(&self) -> usize {
        self.frame.index
    }

    fn abandon(&mut self) {
        self.frame_inner.pgid = PGID_NULL;
        self.frame_inner.state = FrameState::Evictable;
    }

    /// Sets checksum and pgid on the page header prefix and marks the frame as dirty
    /// NOTE This should only be done once! We will panic if we call this on a dirty frame
    /// NOTE This must be called even if immediately before a write-out, because we set the header
    /// fields with it
    fn mark_dirty(&mut self, txid: u64) {
        let pgid = self.get_pgid();
        mooo_assert!(pgid_valid(pgid));
        mooo_assert!(txid != NULL_HIGH_TXID);

        mooo_assert!(self.frame_inner.state == FrameState::InTx);
        self.frame_inner.state = FrameState::Dirty;

        let header = PagePrefix::mut_from_prefix(self.buf);
        header.pgid.set(pgid);
        header.txid.set(txid);

        // Checksum must computed after other sets!
        let checksum = compute_checksum(&self.buf[CHECKSUM_START_OFFSET..]);
        let header = PagePrefix::mut_from_prefix(self.buf);
        header.csum.set(checksum);
    }
}

// ------------ RdHdl ------------------------------------------------------------------------------

/// Shared frame read-handle
pub(super) struct RdHdl<'pager> {
    pager:          &'pager Pager,
    frame:          &'pager FrameHeader,
    frame_inner:    LatchReadGuard<'pager, FrameInner>,
    pub(super) buf: &'pager [u8; PAGE_SIZE],
}

impl<'pager> RdHdl<'pager> {
    /// SAFETY frame_guard must be acquired from frame with index `index`
    unsafe fn from_pager_index(
        pager: &'pager Pager, index: usize, frame_guard: LatchReadGuard<'pager, FrameInner>,
    ) -> Self {
        let frame = &pager.frames[index];
        // SAFETY as long as the frame_guard has been acquired from this frame (frame with `index`)
        // then we know we effectively have a read-lock on this data
        let buf = unsafe { &*pager.pages[index].0.get() };
        Self { pager: pager, frame: frame, frame_inner: frame_guard, buf: buf }
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

// ------------ Thread-Local Tx Registry ------------------------------------------------------

mod tx_registry {
    use std::sync::atomic::AtomicU64;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use super::NULL_HIGH_TXID;
    use crate::mooo_assert;

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
        tx_registry::deregister();
    }
}

impl ReadTx<'_> {
    pub(super) fn get_catalog_root_pgid(&self) -> u64 {
        self.superblock.pgid_catalog.get()
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
    /// NOTE it is the implementors job to set the `pgid` of this handed our WrHdl
    fn get_page_write<'op>(&'op mut self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr>;
    fn get_page_alloc<'op>(&'op mut self) -> Result<WrHdl<'tx>, PagerErr>;
    /// NOTE drop corresponding `WrHdl`/`RdHdl` before calling this!
    fn free_page(&mut self, pgid: u64);
}

impl Drop for WriteTx<'_> {
    fn drop(&mut self) {
        tx_registry::deregister();
    }
}

/// A write-tx that uses bump-allocation only
pub(super) struct WriteTx<'tx> {
    pager:           &'tx Pager,
    superblock:      SuperblockHeader,
    pages_allocated: HashMap<u64, usize>,
    pages_freed:     Vec<u64>,
    pages_free_used: Vec<FreeEntry>,

    count_freelist_used: usize,
    pgid_freelist_old:   u64,

    _writer_tx_lock: MutexGuard<'tx, ()>,
}

impl<'tx> WriteTx<'tx> {
    /// (should_write, should_fsync)
    fn durability_tuple(durability: Durability) -> (bool, bool) {
        match durability {
            Durability::Lazy => (false, false),
            Durability::Flush => (true, false),
            Durability::Sync => (true, true),
        }
    }

    pub(super) fn get_catalog_root_pgid(&self) -> u64 {
        self.superblock.pgid_catalog.get()
    }

    pub(super) fn set_catalog_root_pgid(&mut self, pgid: u64) {
        self.superblock.pgid_catalog.set(pgid);
    }

    fn freelist_prev_next(&mut self) -> Result<Option<FreeEntry>, PagerErr> {
        if self.pgid_freelist_old == PGID_NULL {
            return Ok(None);
        }

        let freelist_old = Btree::from_pgid(self.pgid_freelist_old);
        match freelist_old.freelist_get_index(self, self.count_freelist_used)? {
            None => {
                self.pgid_freelist_old = PGID_NULL;
                Ok(None)
            }
            Some(entry) => {
                self.count_freelist_used += 1;
                Ok(Some(entry))
            }
        }
    }

    fn freelist_insert(&mut self, pgid: u64) -> Result<(), PagerErr> {
        let freelist_head_pgid = self.superblock.pgid_freelist.get();
        let mut freelist = if freelist_head_pgid == PGID_NULL {
            Btree::new(self)?
        } else {
            Btree::from_pgid(freelist_head_pgid)
        };

        let entry = FreeEntry::new(self.superblock.txid.get(), pgid);
        freelist.insert(self, entry.as_bytes(), pgid)?;
        self.superblock.pgid_freelist = freelist.get_root_pgid().into();
        Ok(())
    }

    fn freelist_delete(&mut self, entry: FreeEntry) -> Result<(), PagerErr> {
        let freelist_head_pgid = self.superblock.pgid_freelist.get();
        let mut freelist = if freelist_head_pgid == PGID_NULL {
            Btree::new(self)?
        } else {
            Btree::from_pgid(freelist_head_pgid)
        };

        freelist.delete(self, entry.as_bytes())?;
        self.superblock.pgid_freelist = freelist.get_root_pgid().into();
        Ok(())
    }

    fn freelist_count(&self) -> Result<usize, PagerErr> {
        let freelist_head_pgid = self.superblock.pgid_freelist.get();
        if freelist_head_pgid == PGID_NULL {
            return Ok(0);
        } else {
            Btree::from_pgid(freelist_head_pgid).len(self)
        }
    }

    pub(super) fn commit(mut self, durability: Durability) -> Result<(), PagerErr> {
        let (should_write, should_fsync) = Self::durability_tuple(durability);

        // write freed pages to freelist
        // this can free more pages (of the old freelist) and also allocate new pages
        while !self.pages_free_used.is_empty() || !self.pages_freed.is_empty() {
            while let Some(entry_reused) = self.pages_free_used.pop() {
                self.freelist_delete(entry_reused)?;
            }
            while let Some(pgid_freed) = self.pages_freed.pop() {
                self.freelist_insert(pgid_freed)?;
            }
        }

        eprintln!("freelist count {}", self.freelist_count()?);

        // mostly io after this point, as well as superblock swap

        // write "created" pages (written to pages)
        for &frame_index in self.pages_allocated.values() {
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

        *self.pager.superblock_curr.write().unwrap() = self.superblock.clone();

        eprintln!("--- done COMMIT tx{} ---", self.superblock.txid.get());
        Ok(())
    }
}

// ------------ Allocator --------------------------------------------------------------------------

impl<'tx> PageReader<'tx> for WriteTx<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_frame_read_pgid(pgid)
    }
}

impl<'tx> PageWriter<'tx> for WriteTx<'tx> {
    fn free_page(&mut self, pgid: u64) {
        self.pages_freed.push(pgid);
    }

    /// Bump allocates - also adds page to our dirty-page linked list
    fn get_page_alloc<'op>(&'op mut self) -> Result<WrHdl<'tx>, PagerErr> {
        let pgid = match self.freelist_prev_next()? {
            Some(entry) => {
                eprintln!("ALLOC list tx{} pg{}", self.superblock.txid.get(), entry.pgid.get(),);
                self.pages_free_used.push(entry);
                entry.pgid.get()
            }
            None => {
                let pgid = self.superblock.pgid_bump_next.get();
                eprintln!("ALLOC bump tx{} pg{}", self.superblock.txid.get(), pgid);
                self.superblock.pgid_bump_next.add_assign(1);
                pgid
            }
        };

        let whdl = self.pager.get_frame_write_pgid(pgid)?;
        self.pages_allocated.insert(pgid, whdl.get_frame_index());
        Ok(whdl)
    }

    /// should return a writeable new page, or a writeable copy of an existing page (depending on
    /// pgid)
    fn get_page_write<'op>(&'op mut self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(&index) = self.pages_allocated.get(&pgid) {
            // this is already a new page per our writetx
            return Ok(self.pager.get_frame_write_index(index));
        }

        // we need to CoW
        let old_rhdl = self.get_page_read(pgid)?;
        let new_whdl = self.get_page_alloc()?;
        new_whdl.buf.copy_from_slice(old_rhdl.buf);
        self.free_page(pgid);

        Ok(new_whdl)
    }
}
