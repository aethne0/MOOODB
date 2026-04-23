use std::cell::RefCell;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs::File;
use std::ops::AddAssign;
use std::os::unix::fs::FileExt;

use super::compute_checksum;
use super::hash_u64_modulo;
use super::page_base::PagePrefix;
use super::page_superblock::*;
use super::pgid_valid;
use super::serialization::*;
use super::PAGE_SIZE;
use super::PGID_NULL;
use crate::mooo_assert;
use crate::sync::*;

const SHARD_CNT: usize = 256;
const FIRST_TX_ID: u64 = 1;

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
                .get_page_write(next_superblock_pgid, false)
                .expect("io error on superblock initialization");
            whdl.buf.fill(0);
            pgr.io_write(&mut whdl, 0).expect("io error on superblock initialization");
        }

        let header = {
            // write actua first superblock
            let mut whdl = pgr
                .get_page_write(superblock_pgid, false)
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
            pgr.io_write(&mut whdl, FIRST_TX_ID).expect("io error on superblock initialization");
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
            Ok(_) => Some(unsafe {
                WrHdl::from_pager_index(self, index, self.tx_id.load(Ordering::Relaxed))
            }),
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
        unsafe { WrHdl::from_pager_index(self, index, self.tx_id.load(Ordering::Relaxed)) }
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn try_pin_read(&self, index: usize, expected_pgid: u64) -> Option<RdHdl<'_>> {
        let frame = &self.frames[index];

        if *frame.loading.read().unwrap() != expected_pgid {
            // This was evicted between the time we got it from the dir and the time we got a
            // read-lock - caller will have to retry
            return None;
        }

        frame
            .pins
            .try_update(Ordering::Release, Ordering::Acquire, |prev| {
                if prev >= 0 {
                    Some(prev + 1)
                } else {
                    // Someone has a write lock on this frame
                    None
                }
            })
            .map(|_| unsafe { RdHdl::from_pager_index(self, index) })
            .ok()
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
    #[must_use = "must handle error"]
    fn io_write(&self, whdl: &mut WrHdl<'_>, txid: u64) -> Result<(), PagerErr> {
        let pgid = whdl.get_pgid();
        mooo_assert!(pgid_valid(pgid));

        {
            let header = PagePrefix::mut_from_prefix(whdl.buf);
            header.pgid.set(pgid);
            header.txid.set(txid);
        }
        // Checksum must computed after other sets!
        {
            let checksum = compute_checksum(&whdl.buf[size_of::<SerializedU32>()..]);
            let header = PagePrefix::mut_from_prefix(whdl.buf);
            header.checksum.set(checksum);
        }

        self.file
            .write_at(whdl.buf, pgid * PAGE_SIZE as u64)
            .map(|_| {})
            .map_err(|e| PagerErr::Io(e.kind()))
    }

    #[must_use = "must handle error"]
    fn io_read(&self, whdl: &mut WrHdl<'_>, pgid: u64) -> Result<(), PagerErr> {
        mooo_assert!(pgid_valid(pgid));

        self.file
            .read_exact_at(whdl.buf, pgid * PAGE_SIZE as u64)
            .map_err(|e| PagerErr::Io(e.kind()))?;

        let checksum = compute_checksum(&whdl.buf[size_of::<SerializedU32>()..]);
        {
            let header = PagePrefix::mut_from_prefix(whdl.buf);
            // TODO should just be an error eventually
            mooo_assert!(header.checksum.get() == checksum, "checksums must match");
        }

        Ok(())
    }

    // ------------ pages --------------------------------------------------------------------------

    #[must_use = "no side effects"]
    fn scan_for_eviction_candidate(&self) -> usize {
        let mut checked_count = 0; // for spin hint heuristics

        loop {
            let frame_idx = self.eviction_hand.fetch_add(1, Ordering::Relaxed) % self.frames.len();
            let frame = &self.frames[frame_idx];

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

            checked_count += 1;
            if checked_count == self.frames.len() {
                std::hint::spin_loop();
                checked_count = 0;
            }
        }
    }

    #[must_use = "RAII RdHdl releases when dropped"]
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'_>, PagerErr> {
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
                            Some(whdl) => break whdl,
                        }
                    };

                    // this can be contested, because someone may have found this frame in the dir,
                    // and is calling `pin_read` and checking the pgid
                    let mut loading_guard = whdl.frame.loading.write().unwrap();
                    let frame_pgid = std::mem::replace(&mut *loading_guard, pgid);

                    dir.insert(pgid, whdl.frame.index);
                    drop(dir);

                    // remove from old dir if needed
                    // It is ok if threads find this page before we do this, because we are holding the
                    // loading lock, and once we release it they will see the new (to them unexpected)
                    // pgid and they'll retry
                    let mut old_dir =
                        self.shard_dirs[hash_u64_modulo(frame_pgid, SHARD_CNT)].lock().unwrap();
                    old_dir.remove(&frame_pgid);
                    drop(old_dir);

                    self.io_read(&mut whdl, pgid)?;

                    let rhdl = self.pin_downgrade(whdl);
                    drop(loading_guard);
                    return Ok(rhdl);
                }
            }
        }
    }

    // TODO its possible were never passing should_load = true, because writetx just keeps a list of
    // frame indicies to get writeguards again
    /// gets an exclusive WHdl to a frame with `pgid`.
    /// Note: this method will initialize the `WHdl`'s `pgid` field
    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_page_write(&self, pgid: u64, should_load: bool) -> Result<WrHdl<'_>, PagerErr> {
        mooo_assert!(pgid_valid(pgid));
        let mut dir = self.shard_dirs[hash_u64_modulo(pgid, SHARD_CNT)].lock().unwrap();

        match dir.get(&pgid) {
            Some(&frame_index) => {
                let mut whdl = self.pin_write(frame_index);
                whdl.pgid = pgid;
                return Ok(whdl);
            }
            None => {
                let mut whdl = loop {
                    let free_frame_index = self.scan_for_eviction_candidate();
                    match self.try_pin_write(free_frame_index) {
                        None => continue,
                        Some(mut whdl) => {
                            whdl.pgid = pgid;
                            break whdl;
                        }
                    }
                };

                let mut loading_guard = whdl.frame.loading.write().unwrap();
                let frame_pgid = std::mem::replace(&mut *loading_guard, pgid);

                dir.insert(pgid, whdl.frame.index);
                drop(dir);

                let mut old_dir =
                    self.shard_dirs[hash_u64_modulo(frame_pgid, SHARD_CNT)].lock().unwrap();
                old_dir.remove(&frame_pgid);
                drop(old_dir);

                if should_load {
                    self.io_read(&mut whdl, pgid)?;
                }

                whdl.pgid = pgid;
                return Ok(whdl);
            }
        };
    }

    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_frame_write(&self, frame_index: usize) -> WrHdl<'_> {
        let mut whdl = self.try_pin_write(frame_index).expect("must be uncontested");
        whdl.pgid = *self.frames[frame_index].loading.read().unwrap(); // this could be better
        whdl
    }

    #[must_use = "RAII ReadTxHdl releases when dropped"]
    pub(super) fn read_tx<'tx>(&'tx self) -> ReadTxHdl<'tx> {
        let superblock = {
            // we need to hold this guard while we put our value in the registry
            let curr_guard = self.curr_superblock.read().expect("todo");
            let current = curr_guard.clone();

            let txid = current.txid.get();
            thread_local_tx_registry::register(txid);

            current
        };

        ReadTxHdl { pager: self, superblock }
    }

    #[must_use = "RAII WriteTxHdl releases when dropped"]
    pub(super) fn write_tx<'tx>(&'tx self) -> WriteTxHdlBump<'tx> {
        let lock = self.write_tx_lock.lock().unwrap();

        let mut superblock = self.curr_superblock.read().expect("todo").clone();
        let prev_pgid = superblock.pgid.get();
        superblock.txid += 1;
        superblock.pgid.set((prev_pgid + 1) % 2);

        WriteTxHdlBump {
            pager: self,
            inner: RefCell::new(WriteTxHdlInner {
                superblock:    superblock,
                created_pages: HashMap::new(),
            }),
            _lock: lock,
        }
    }
}

// -------------------------------------------------------------------------------------------------
// *            Frame Definitions                                                                  *
// -------------------------------------------------------------------------------------------------

#[repr(align(4096))]
struct FrameBuffer(UnsafeCell<[u8; PAGE_SIZE]>);

impl FrameBuffer {
    #[must_use]
    fn zeros() -> Self {
        Self(UnsafeCell::new([0; PAGE_SIZE]))
    }
}

#[repr(align(64))]
struct FrameHeader {
    index:   usize,
    /// Negative is write, positive is read - write is exclusive
    pins:    AtomicI64,
    usage:   AtomicU64,
    loading: RwLock<u64>,
}

impl FrameHeader {
    fn new(index: usize) -> Self {
        Self {
            index:   index,
            pins:    0.into(),
            usage:   0.into(),
            loading: RwLock::new(PGID_NULL), // TODO might not be using this value anymore
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
    pgid:           u64,
}

impl<'pager> WrHdl<'pager> {
    unsafe fn from_pager_index(pager: &'pager Pager, index: usize, txid: u64) -> Self {
        let frame = &pager.frames[index];
        let buf = unsafe { &mut *pager.pages[index].0.get() };
        Self { pager: pager, frame: frame, buf: buf, txid, pgid: PGID_NULL }
    }

    pub(super) fn flush(&mut self) -> Result<(), PagerErr> {
        self.pager.io_write(self, self.txid)
    }

    pub(super) fn get_pgid(&self) -> u64 {
        mooo_assert!(pgid_valid(self.pgid));
        self.pgid
    }

    pub(super) fn get_frame_index(&self) -> usize {
        self.frame.index
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
pub enum PagerErr {
    Io(std::io::ErrorKind),
}

// -------------------------------------------------------------------------------------------------
// *            Tx Definitions                                                                     *
// -------------------------------------------------------------------------------------------------

pub(super) enum Durability {
    None,
    Flush,
    Sync,
}

// ------------ Traits -----------------------------------------------------------------------------

pub(super) trait PageReader<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr>;
    fn get_catalog_root_id(&self) -> u64;
}

pub(super) trait PageWriter<'tx> {
    /// This will give out a writeable frame with a new, free `pgid`
    ///
    /// Note: it is the implementors job to set the `pgid` of this handed our WrHdl
    fn get_page_alloc(&self) -> Result<WrHdl<'tx>, PagerErr>;
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
    fn get_page_write(&self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr>;
    fn update_catalog_root_id(&self, pgid: u64);
}

// ------------ ReadTx -----------------------------------------------------------------------------

pub(super) struct ReadTxHdl<'tx> {
    pager:      &'tx Pager,
    superblock: SuperblockHeader,
}

impl Drop for ReadTxHdl<'_> {
    fn drop(&mut self) {
        thread_local_tx_registry::deregister();
    }
}

impl<'tx> PageReader<'tx> for ReadTxHdl<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_page_read(pgid)
    }

    fn get_catalog_root_id(&self) -> u64 {
        self.superblock.catalog_head_pgid.get()
    }
}

// ------------ WriteTx ----------------------------------------------------------------------------

/// A write-tx that uses bump-allocation only
pub(super) struct WriteTxHdlBump<'tx> {
    pager:            &'tx Pager,
    pub(super) inner: RefCell<WriteTxHdlInner>,
    _lock:            MutexGuard<'tx, ()>,
}

pub(super) struct WriteTxHdlInner {
    pub(super) superblock:    SuperblockHeader,
    pub(super) created_pages: HashMap<u64, usize>,
}

impl WriteTxHdlBump<'_> {
    pub(super) fn commit(self, durability: Durability) -> Result<(), PagerErr> {
        let inner = self.inner.borrow_mut();

        for &frame_index in inner.created_pages.values() {
            let mut whdl = self.pager.get_frame_write(frame_index);
            // TODO check durability
            // btw we need a version of this that will update pgid and tx_id and stuff without
            // actually writing
            self.pager.io_write(&mut whdl, inner.superblock.txid.get())?;
        }

        let sb_pgid = inner.superblock.pgid.get();
        let mut whdl = self.pager.get_page_write(sb_pgid, false)?;
        copy_superblock_to_page(whdl.buf, &inner.superblock);
        self.pager.io_write(&mut whdl, inner.superblock.txid.get())?;

        // these don't need to be atomic - we are holding _lock anyway
        *self.pager.curr_superblock.write().unwrap() = inner.superblock.clone();
        self.pager.tx_id.store(inner.superblock.txid.get(), Ordering::Relaxed);

        Ok(())
    }
}

impl<'tx> PageReader<'tx> for WriteTxHdlBump<'tx> {
    fn get_page_read(&self, pgid: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_page_read(pgid)
    }

    fn get_catalog_root_id(&self) -> u64 {
        self.inner.borrow().superblock.catalog_head_pgid.get()
    }
}

impl<'tx> PageWriter<'tx> for WriteTxHdlBump<'tx> {
    fn update_catalog_root_id(&self, pgid: u64) {
        self.inner.borrow_mut().superblock.catalog_head_pgid.set(pgid);
    }

    /// Bump allocates - also adds page to our dirty-page linked list
    fn get_page_alloc(&self) -> Result<WrHdl<'tx>, PagerErr> {
        let mut inner = self.inner.borrow_mut();
        let pgid = inner.superblock.alloc_bump_next_pgid.get();
        inner.superblock.alloc_bump_next_pgid.add_assign(1);
        let whdl = self.pager.get_page_write(pgid, false)?;
        inner.created_pages.insert(pgid, whdl.get_frame_index());
        Ok(whdl)
    }

    /// should return a writeable new page, or a writeable copy of an existing page (depending on
    /// pgid)
    fn get_page_write(&self, pgid: u64) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(&index) = self.inner.borrow().created_pages.get(&pgid) {
            // this is already a new page per our writetx
            return Ok(self.pager.get_frame_write(index));
        }

        // we need to Copy-on-Write
        let old_rhdl = self.get_page_read(pgid)?;
        let new_whdl = self.get_page_alloc()?;
        new_whdl.buf.copy_from_slice(old_rhdl.buf);

        Ok(new_whdl)
    }
}

// -------------------------------------------------------------------------------------------------
// *            Thread-Local Read-tx Registry                                                      *
// -------------------------------------------------------------------------------------------------

mod thread_local_tx_registry {
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
