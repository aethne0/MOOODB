// TODO all these unsafe bits should just be one method that gets the index and the &but at the same
// time to ensure its safe

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
use crate::fixed_array::StackArray;
use crate::mooo_assert;

// -------------------------------------------------------------------------------------------------
//  ▄▄▄· ▄▄▄·  ▄▄ • ▄▄▄ .▄▄▄
// ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪▀▄.▀·▀▄ █·
//  ██▀·▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄▐▀▀▄
// ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌▐█•█▌  Page Buffer, IO, Tx Management
// .▀    ▀  ▀ ·▀▀▀▀  ▀▀▀ .▀  ▀
// -------------------------------------------------------------------------------------------------

const ON_DISK_VERSION: u64 = 1;
const SHARD_CNT: usize = 256;
const TXID_NULL_HIGH: u64 = u64::MAX;

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

    // ------------ tx -----------------------------------------------------------------------------

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
            pager:                  self,
            superblock:             superblock,
            pages_allocated:        HashMap::new(),
            pages_freed:            StackArray::new(),
            fl_prev_used_ptr:       0,
            fl_prev_dltd_ptr:       0,
            fl_prev_pgid:           freelist_pgid.get(),
            should_cleanup_on_drop: true,
            _writer_tx_lock:        lock,
        }
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

    // ---------------------------------------------------------------------------------------------
    //                                                       ▄ .▄ ▄▄▄·  ▐ ▄ ·▄▄▄▄  ▄▄▌  ▄▄▄ ..▄▄ ·
    //                                                      ██▪▐█▐█ ▀█ •█▌▐███▪ ██ ██•  ▀▄.▀·▐█ ▀.
    //                                                      ██▀▐█▄█▀▀█ ▐█▐▐▌▐█· ▐█▌██▪  ▐▀▀▪▄▄▀▀▀█▄
    //  Frame handles & page-dir management                 ██▌▐▀▐█ ▪▐▌██▐█▌██. ██ ▐█▌▐▌▐█▄▄▌▐█▄▪▐█
    //                                                      ▀▀▀ · ▀  ▀ ▀▀ █▪▀▀▀▀▀• .▀▀▀  ▀▀▀  ▀▀▀▀
    // ---------------------------------------------------------------------------------------------
    // NOTE To keep things easy to reason about, these should be the only places where we call lock
    // methods on the frame latch. By extension these will also be the only palces we construct
    // WrHdl and RdHdl (other than WrdHdl::Downgrade, but that doesnt take a new lock)

    // Does not block
    /// This increments the usage counter if the lock is acquired.
    #[must_use = "RAII WrHdl releases when dropped"]
    fn latch_try_write(&self, index: usize) -> Option<WrHdl<'_>> {
        let frame = &self.frames[index];

        // this is the only place where latch.write() / latch.try_write() is called
        let Some(frame_guard) = frame.latch.try_write() else {
            return None;
        };

        frame.usage.fetch_add(1, Ordering::Relaxed);
        Some(WrHdl {
            frame:       frame,
            frame_inner: frame_guard,
            // SAFETY as long as the frame_guard has been acquired from this frame (frame with `index`)
            // then we know we effectively have a write-lock on this data
            buf:         unsafe { &mut *self.pages[index].0.get() },
        })
    }

    /// Blocks - the "try" refers to the fact that the page may have been evicted while we were
    /// waiting to get a lock but since we looked it up in the dir (retrieved `index`)
    /// This increments the usage counter.
    #[must_use = "RAII RdHdl releases when dropped"]
    fn latch_read_and_check(&self, index: usize, pgid: u64) -> Option<RdHdl<'_>> {
        let frame = &self.frames[index];

        // this is the only place where latch.read() / latch.try_read() is called
        let frame_guard = frame.latch.read();
        if frame_guard.pgid != pgid {
            // This was evicted between the time we got it from the dir and the time we got a
            // read-lock - caller will have to retry
            return None;
        }

        frame.usage.fetch_add(1, Ordering::Relaxed);
        Some(RdHdl {
            frame:       frame,
            frame_inner: frame_guard,
            // SAFETY as long as the frame_guard has been acquired from this frame (frame with `index`)
            // then we know we effectively have a read-lock on this data
            buf:         unsafe { &*self.pages[index].0.get() },
        })
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn scan_for_eviction_candidate(&self) -> WrHdl<'_> {
        let mut checked_count = 0;
        loop {
            if checked_count == self.frames.len() {
                checked_count = 0;
                std::hint::spin_loop();
            }
            checked_count += 1;

            let frame_index =
                self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.frames.len();

            let Some(whdl) = self.latch_try_write(frame_index) else {
                // someones reading|writing this frame
                continue;
            };

            if whdl.frame_inner.state == FrameState::InTx {
                // frame is part of an in-progress write-tx
                continue;
            }

            let frame_usage_ctr = whdl
                .frame
                .usage
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |old| Some(old.saturating_sub(1)))
                .unwrap();
            mooo_assert!(frame_usage_ctr != u64::MAX);

            if frame_usage_ctr == 1 {
                // We check for 1, not 0, because it was incremented by `latch_try_write`
                return whdl;
            }
        }
    }

    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_frame_write_index(&self, frame_index: usize) -> WrHdl<'_> {
        let whdl = self.latch_try_write(frame_index).expect("must be uncontested");
        whdl
    }

    // ------------ frame handles + pgid directories -----------------------------------------------
    // These methods handles managing the the pgid -> frame_index directories, during eviction,
    // population and initialization.

    #[must_use = "RAII RdHdl releases when dropped"]
    fn get_frame_read_pgid(&self, pgid: u64) -> Result<RdHdl<'_>, PagerErr> {
        mooo_assert!(pgid_valid(pgid));
        loop {
            let mut dir = self.shard_dirs[hash_u64_modulo(pgid, SHARD_CNT)].lock().unwrap();

            match dir.get(&pgid) {
                Some(&frame_index) => {
                    match self.latch_read_and_check(frame_index, pgid) {
                        None => {
                            // someone took this frame and changed its pgid since we checked the dir, so
                            // we will abandon it and try again
                            continue;
                        }
                        Some(rhdl) => {
                            return Ok(rhdl);
                        }
                    }
                }
                None => {
                    // eviction path - these comments apply to `get_page_write` as well
                    let mut whdl = self.scan_for_eviction_candidate();
                    let frame_pgid = replace(&mut whdl.frame_inner.pgid, pgid);

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
                    if whdl.frame_inner.state == FrameState::Dirty {
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

                    return Ok(whdl.downgrade());
                }
            }
        }
    }

    /// Gets an exclusive WHdl to a frame with `pgid`.
    /// We should NOT be calling this method on a pgid that is readable by other threads!
    /// Note: this method will initialize the `WHdl`'s `pgid` field
    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_frame_write_pgid(&self, pgid: u64) -> Result<WrHdl<'_>, PagerErr> {
        mooo_assert!(pgid_valid(pgid));
        let mut dir = self.shard_dirs[hash_u64_modulo(pgid, SHARD_CNT)].lock().unwrap();

        match dir.get(&pgid) {
            Some(&frame_index) => {
                let mut whdl = self.latch_try_write(frame_index).expect("should be uncontested");
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

    /// This will give up our latch and remove the frame from the pgid -> frame_index directory, and
    /// set the state so it is no longer `InTx` such that it can be evicted and reused.
    /// NOTE lock must not be held on this frame when this is called
    fn abandon_allocated_frame(&self, frame_index: usize) {
        let mut whdl = self.latch_try_write(frame_index).expect("must be uncontested");
        let pgid = replace(&mut whdl.frame_inner.pgid, PGID_NULL);
        mooo_assert!(pgid_valid(pgid));
        let entry = self.shard_dirs[hash_u64_modulo(pgid, SHARD_CNT)].lock().unwrap().remove(&pgid);
        mooo_assert!(entry.is_some(), "should have been resident");
        whdl.frame_inner.state = FrameState::Evictable;
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
    pub(super) buf: &'pager mut [u8; PAGE_SIZE],
    frame:          &'pager FrameHeader,
    frame_inner:    LatchWriteGuard<'pager, FrameInner>,
}

impl<'pager> WrHdl<'pager> {
    pub(super) fn get_pgid(&self) -> u64 {
        let pgid = self.frame_inner.pgid;
        mooo_assert!(pgid_valid(pgid));
        pgid
    }

    /// Sets checksum and pgid on the page header prefix and marks the frame as dirty
    /// NOTE This should only be done once! We will panic if we call this on a dirty frame
    /// NOTE This must be called even if immediately before a write-out, because we set the header
    /// fields with it
    fn mark_dirty(&mut self, txid: u64) {
        let pgid = self.get_pgid();
        mooo_assert!(txid != TXID_NULL_HIGH);
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

    /// atomically downgrades a WrHdl to a RdHdl - no writers will acquire a lock on this frame
    /// before we have a read lock.
    #[must_use = "RAII RdHdl releases when dropped"]
    fn downgrade(self) -> RdHdl<'pager> {
        let WrHdl { frame, frame_inner, buf } = self;
        RdHdl { frame: frame, frame_inner: latch_downgrade(frame_inner), buf: &*buf }
    }
}

// ------------ RdHdl ------------------------------------------------------------------------------

/// Shared frame read-handle
pub(super) struct RdHdl<'pager> {
    frame:          &'pager FrameHeader,
    frame_inner:    LatchReadGuard<'pager, FrameInner>,
    pub(super) buf: &'pager [u8; PAGE_SIZE],
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PagerErr {
    Io(std::io::ErrorKind),
    /// `page_id` or `checksum` did not match
    Integrity,
}

// -------------------------------------------------------------------------------------------------
// ▄▄▄▄▄▐▄• ▄
// •██   █▌█▌▪
//  ▐█.▪ ·██·
//  ▐█▌·▪▐█·█▌  WriteTx & ReadTx
//  ▀▀▀ •▀▀ ▀▀
// -------------------------------------------------------------------------------------------------

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
    fn free_page(&mut self, pgid: u64) -> Result<(), PagerErr>;
}

// -------------------------------------------------------------------------------------------------
//                                         ▄▄▄▄▄▐▄• ▄     ▄▄▄  ▄▄▄ . ▄▄ • ▪  .▄▄ · ▄▄▄▄▄▄▄▄   ▄· ▄▌
//                                         •██   █▌█▌▪    ▀▄ █·▀▄.▀·▐█ ▀ ▪██ ▐█ ▀. •██  ▀▄ █·▐█▪██▌
//                                          ▐█.▪ ·██·     ▐▀▀▄ ▐▀▀▪▄▄█ ▀█▄▐█·▄▀▀▀█▄ ▐█.▪▐▀▀▄ ▐█▌▐█▪
//  Thread-local Tx Registry                ▐█▌·▪▐█·█▌    ▐█•█▌▐█▄▄▌▐█▄▪▐█▐█▌▐█▄▪▐█ ▐█▌·▐█•█▌ ▐█▀·.
//                                          ▀▀▀ •▀▀ ▀▀    .▀  ▀ ▀▀▀ ·▀▀▀▀ ▀▀▀ ▀▀▀▀  ▀▀▀ .▀  ▀  ▀ •
// -------------------------------------------------------------------------------------------------

mod tx_registry {
    use std::sync::atomic::AtomicU64;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use super::TXID_NULL_HIGH;
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
        [const { AtomicU64::new(TXID_NULL_HIGH) }; MAX_THREADS];
    thread_local! {
        static THREAD_INDEX: usize = get_next_thread_local_index();
    }

    pub(super) fn register(tx_id: u64) {
        mooo_assert!(tx_id != TXID_NULL_HIGH);
        THREAD_INDEX.with(|&thread_index| {
            COUNTERS[thread_index]
                .compare_exchange(TXID_NULL_HIGH, tx_id, Ordering::Release, Ordering::Relaxed)
                .expect("tried to take re-entrant read guard");
        });
    }
    pub(super) fn deregister() {
        THREAD_INDEX.with(|&thread_index| {
            COUNTERS[thread_index].store(TXID_NULL_HIGH, Ordering::Release);
        });
    }

    pub(super) fn get_min() -> u64 {
        // its ok if our max index gets stale, because the new thread we didnt see will definitely
        // have a tx_id GE to any of these
        let count = NEXT_ID.load(Ordering::Relaxed);
        let mut earliest = TXID_NULL_HIGH;
        for i in 0..count {
            earliest = earliest.min(COUNTERS[i].load(Ordering::Acquire));
        }
        earliest
    }
}

// -------------------------------------------------------------------------------------------------
//                                                               ▄▄▄  ▄▄▄ . ▄▄▄· ·▄▄▄▄  ▄▄▄▄▄▐▄• ▄
//                                                               ▀▄ █·▀▄.▀·▐█ ▀█ ██▪ ██ •██   █▌█▌▪
//                                                               ▐▀▀▄ ▐▀▀▪▄▄█▀▀█ ▐█· ▐█▌ ▐█.▪ ·██·
//  ReadTx                                                       ▐█•█▌▐█▄▄▌▐█ ▪▐▌██. ██  ▐█▌·▪▐█·█▌
//                                                               .▀  ▀ ▀▀▀  ▀  ▀ ▀▀▀▀▀•  ▀▀▀ •▀▀ ▀▀
// -------------------------------------------------------------------------------------------------

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

// -------------------------------------------------------------------------------------------------
//                                                            ▄▄▌ ▐ ▄▌▄▄▄  ▪  ▄▄▄▄▄▄▄▄ .▄▄▄▄▄▐▄• ▄
//                                                            ██· █▌▐█▀▄ █·██ •██  ▀▄.▀·•██   █▌█▌▪
//                                                            ██▪▐█▐▐▌▐▀▀▄ ▐█· ▐█.▪▐▀▀▪▄ ▐█.▪ ·██·
//  WriteTx                                                   ▐█▌██▐█▌▐█•█▌▐█▌ ▐█▌·▐█▄▄▌ ▐█▌·▪▐█·█▌
//                                                             ▀▀▀▀ ▀▪.▀  ▀▀▀▀ ▀▀▀  ▀▀▀  ▀▀▀ •▀▀ ▀▀
// -------------------------------------------------------------------------------------------------

/// A write-tx that uses bump-allocation only
pub(super) struct WriteTx<'tx> {
    pager:                  &'tx Pager,
    superblock:             SuperblockHeader,
    /// This gets set after successful commit, to stop some drop cleanup stuff from happening
    should_cleanup_on_drop: bool,
    _writer_tx_lock:        MutexGuard<'tx, ()>,

    /// This will writeout to our new freelist if its full
    pages_freed:      StackArray<u64, 127>,
    /// root pgid of our old snapshotted freelist, we will be taking from this for allocations
    fl_prev_pgid:     u64,
    /// number of allocations we've taken from this freelist - we take them in order up to either
    /// the end or up to (but not including) the txid of the lowest current registered tx
    fl_prev_used_ptr: usize,
    /// number of allocations from the old freelist that we've deleted from our new version of the
    /// freelist - see `fl_prev_used_ptr`
    fl_prev_dltd_ptr: usize,
    // TODO rewrite a stack version of this
    // we could simplify this into just an array, but then wed have to do a lookup via the pager
    // every single time we wanted to use one of our own pages, and itd also be much less efficient
    // to check if a given page was created by us (in `get_page_write`).
    pages_allocated:  HashMap<u64, usize>,
}

impl Drop for WriteTx<'_> {
    fn drop(&mut self) {
        if self.should_cleanup_on_drop {
            for (_, &frame_index) in self.pages_allocated.iter() {
                self.pager.abandon_allocated_frame(frame_index);
            }
        }

        tx_registry::deregister();
    }
}

impl<'tx> WriteTx<'tx> {
    pub(super) fn get_catalog_root_pgid(&self) -> u64 {
        self.superblock.pgid_catalog.get()
    }

    pub(super) fn set_catalog_root_pgid(&mut self, pgid: u64) {
        self.superblock.pgid_catalog.set(pgid);
    }

    pub(super) fn commit(mut self, durability: Durability) -> Result<(), PagerErr> {
        let (should_write, should_fsync) = match durability {
            Durability::Lazy => (false, false),
            Durability::Flush => (true, false),
            Durability::Sync => (true, true),
        };

        // write freed pages to freelist
        // this can free more pages (of the old freelist) and also allocate new pages
        self.freelist_apply_changes()?;

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

        self.should_cleanup_on_drop = false;
        *self.pager.superblock_curr.write().unwrap() = self.superblock.clone();
        Ok(())
    }

    // ------------ Freelist stuff -----------------------------------------------------------------

    fn freelist_prev_next(&mut self) -> Result<Option<FreeEntry>, PagerErr> {
        if self.fl_prev_pgid == PGID_NULL {
            return Ok(None);
        }

        let freelist_old = Btree::from_pgid(self.fl_prev_pgid);
        match freelist_old.freelist_get_index(self, self.fl_prev_used_ptr)? {
            Some(entry) => {
                let txid_bound = tx_registry::get_min();
                if entry.txid.get() < txid_bound {
                    self.fl_prev_used_ptr += 1;
                    Ok(Some(entry))
                } else {
                    Ok(None)
                }
            }
            None => Ok(None),
        }
    }

    fn freelist_new_insert(&mut self, pgid: u64) -> Result<(), PagerErr> {
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

    fn freelist_new_delete(&mut self, entry: FreeEntry) -> Result<(), PagerErr> {
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

    fn freelist_apply_changes(&mut self) -> Result<(), PagerErr> {
        while self.fl_prev_dltd_ptr < self.fl_prev_used_ptr || !self.pages_freed.is_empty() {
            while self.fl_prev_dltd_ptr < self.fl_prev_used_ptr {
                let freelist_old = Btree::from_pgid(self.fl_prev_pgid);
                let entry = freelist_old.freelist_get_index(self, self.fl_prev_dltd_ptr)?.unwrap();
                self.freelist_new_delete(entry)?;
                self.fl_prev_dltd_ptr += 1
            }

            while let Some(pgid_freed) = self.pages_freed.pop() {
                self.freelist_new_insert(pgid_freed)?;
            }
        }
        Ok(())
    }
}

// ------------ WriteTx allocator ------------------------------------------------------------------

impl<'tx> PageReader<'tx> for WriteTx<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_frame_read_pgid(pgid)
    }
}

impl<'tx> PageWriter<'tx> for WriteTx<'tx> {
    fn free_page(&mut self, pgid: u64) -> Result<(), PagerErr> {
        if let Some(frame_index) = self.pages_allocated.remove(&pgid) {
            // we allocated this page, so we should abandon it
            self.pager.abandon_allocated_frame(frame_index);
        }

        if self.pages_freed.is_full() {
            self.freelist_apply_changes()?;
        }
        self.pages_freed.push(pgid);
        Ok(())
    }

    /// Bump allocates - also adds page to our dirty-page linked list
    fn get_page_alloc<'op>(&'op mut self) -> Result<WrHdl<'tx>, PagerErr> {
        let pgid = match self.freelist_prev_next()? {
            Some(entry) => entry.pgid.get(),
            None => {
                let pgid = self.superblock.pgid_bump_next.get();
                self.superblock.pgid_bump_next.add_assign(1);
                pgid
            }
        };

        let whdl = self.pager.get_frame_write_pgid(pgid)?;
        self.pages_allocated.insert(pgid, whdl.frame.index);
        Ok(whdl)
    }

    /// returns a writeable new page, or a writeable copy of an existing page - depends on pgid
    fn get_page_write<'op>(&'op mut self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(&index) = self.pages_allocated.get(&pgid) {
            // this is already a new page per our writetx
            return Ok(self.pager.get_frame_write_index(index));
        }

        // we need to CoW
        let old_rhdl = self.get_page_read(pgid)?;
        let new_whdl = self.get_page_alloc()?;
        new_whdl.buf.copy_from_slice(old_rhdl.buf);
        self.free_page(pgid)?;

        Ok(new_whdl)
    }
}
