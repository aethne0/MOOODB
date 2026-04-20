use std::cell::RefCell;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs::File;
use std::mem::offset_of;
use std::ops::AddAssign;
use std::os::unix::fs::FileExt;

use xxhash_rust::xxh3;
use zerocopy::FromBytes;
use zerocopy::FromZeros;
use zerocopy::IntoBytes;

use super::PAGE_ID_NULL;
use super::PAGE_SIZE;
use super::page_base::PagePrefix;
use super::page_superblock::SuperblockHeader;
use crate::mooo_assert;
use crate::sync::*;

//  ▄▄▄· ▄▄▄·  ▄▄ • ▄▄▄ .    ▄▄▄▄· ▄• ▄▌·▄▄▄·▄▄▄▄▄▄ .▄▄▄
// ▐█ ▄█▐█ ▀█ ▐█ ▀ ▪▀▄.▀·    ▐█ ▀█▪█▪██▌▐▄▄·▐▄▄·▀▄.▀·▀▄ █·
//  ██▀·▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄    ▐█▀▀█▄█▌▐█▌██▪ ██▪ ▐▀▀▪▄▐▀▀▄
// ▐█▪·•▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌    ██▄▪▐█▐█▄█▌██▌.██▌.▐█▄▄▌▐█•█▌
// .▀    ▀  ▀ ·▀▀▀▀  ▀▀▀     ·▀▀▀▀  ▀▀▀ ▀▀▀ ▀▀▀  ▀▀▀ .▀  ▀

#[repr(align(4096))]
struct FrameBuffer(UnsafeCell<[u8; PAGE_SIZE]>);
const SHARD_CNT: usize = 256;
const FIRST_TX_ID: u64 = 1;

pub(super) struct Pager {
    file: File,

    frames: Box<[FrameHeader]>,
    pages:  Box<[FrameBuffer]>,

    // these are Mutexs instead of RwLocks because we often have to take a read-lock, then drop it,
    // then try to take a writelock, then double check - because of sharding it is probably faster
    // to just have it be a mutex
    shard_dirs: Box<[Mutex<HashMap<u64, usize>>]>,

    eviction_hand: AtomicUsize,

    tx_id: AtomicU64,

    current:    RwLock<SuperblockHeader>,
    write_lock: Mutex<()>,
}

unsafe impl Sync for Pager {}

impl Pager {
    pub(super) fn new(count: usize, file: File) -> Self {
        let temp_header = SuperblockHeader::new_zeroed();

        let pgr = Self {
            file:          file,
            frames:        (0..count).map(|i| FrameHeader::new(i)).collect(),
            pages:         (0..count).map(|_| FrameBuffer::zeros()).collect(),
            shard_dirs:    (0..SHARD_CNT).map(|_| Mutex::new(HashMap::default())).collect(),
            eviction_hand: 0.into(),
            tx_id:         FIRST_TX_ID.into(),
            write_lock:    Mutex::new(()),
            current:       RwLock::new(temp_header),
        };

        let superblock_page_id = 0;
        // page 0&1 are reserved for superblocks
        let next_page_id = 2;

        let mut w_hdl = pgr
            .get_page_write(superblock_page_id, false)
            .expect("io error on superblock initialization");

        let superblock_header = SuperblockHeader {
            prefix:             PagePrefix::new(superblock_page_id, 0, FIRST_TX_ID),
            version:            1.into(),
            page_size:          (PAGE_SIZE as u16).into(),
            catalog_head_id:    PAGE_ID_NULL.into(),
            alloc_free_head_id: PAGE_ID_NULL.into(),
            alloc_bump_next_id: next_page_id.into(),
            _pad:               [0; 62],
        };

        copy_superblock_to_page(w_hdl.buf, &superblock_header);
        pgr.io_write(&mut w_hdl, FIRST_TX_ID).expect("couldnt initialize superblock to disk");
        drop(w_hdl);

        pgr.current.write().unwrap().clone_from(&superblock_header);
        pgr
    }

    // ------------ frame --------------------------------------------------------------------------

    fn try_pin_write(&self, index: usize) -> Option<WrHdl<'_>> {
        let frame = &self.frames[index];
        match frame.pins.compare_exchange(0, -1, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => Some(unsafe {
                WrHdl::from_pager_index(self, index, self.tx_id.load(Ordering::Relaxed))
            }),
            Err(_) => None,
        }
    }

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

    fn try_pin_read(&self, index: usize, expected_page_id: u64) -> Option<RdHdl<'_>> {
        let frame = &self.frames[index];

        if *frame.loading.read().unwrap() != expected_page_id {
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

    fn pin_downgrade(&self, w_hdl: WrHdl<'_>) -> RdHdl<'_> {
        let index = w_hdl.frame.index;
        std::mem::forget(w_hdl);

        let frame = &self.frames[index];
        let cas_res = frame.pins.compare_exchange(-1, 1, Ordering::AcqRel, Ordering::Acquire);

        mooo_assert!(cas_res.is_ok(), "pin_downgrade should be uncontested");
        unsafe { RdHdl::from_pager_index(self, index) }
    }

    // ------------ io -----------------------------------------------------------------------------

    fn io_write(&self, w_hdl: &mut WrHdl<'_>, tx_id: u64) -> Result<(), PagerErr> {
        mooo_assert!(w_hdl.get_page_id() != PAGE_ID_NULL);

        let page_id = w_hdl.get_page_id();
        let checksum = xxh3::xxh3_64(&w_hdl.buf[offset_of!(PagePrefix, page_id)..]);
        let header = PagePrefix::mut_from_prefix(w_hdl.buf).unwrap().0;
        header.checksum.set(checksum);
        header.page_id.set(page_id);
        header.tx_id.set(tx_id);

        self.file
            .write_at(w_hdl.buf, w_hdl.get_page_id() * PAGE_SIZE as u64)
            .map(|_| {})
            .map_err(|e| PagerErr::Io(e.kind()))
    }

    fn io_read(&self, w_hdl: &mut WrHdl<'_>) -> Result<(), PagerErr> {
        let page_id = w_hdl.get_page_id();
        mooo_assert!(page_id != PAGE_ID_NULL);
        self.file
            .read_exact_at(w_hdl.buf, page_id * PAGE_SIZE as u64)
            .map_err(|e| PagerErr::Io(e.kind()))
    }

    // ------------ pages --------------------------------------------------------------------------

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
    fn get_page_read(&self, page_id: u64) -> Result<RdHdl<'_>, PagerErr> {
        loop {
            let mut dir = self.shard_dirs[shard_hash(page_id)].lock().unwrap();

            match dir.get(&page_id) {
                Some(&frame_index) => match self.try_pin_read(frame_index, page_id) {
                    None => {
                        // we got a stale frame - retry
                        continue;
                    }
                    Some(r_hdl) => {
                        return Ok(r_hdl);
                    }
                },
                None => {
                    // eviction path - these comments apply to `get_page_write` as well
                    let mut w_hdl = loop {
                        let free_frame_index = self.scan_for_eviction_candidate();
                        match self.try_pin_write(free_frame_index) {
                            None => continue,
                            Some(w_hdl) => break w_hdl,
                        }
                    };

                    // this can be contested, because someone may have found this frame in the dir,
                    // and is calling `pin_read` and checking the page_id
                    let mut loading_guard = w_hdl.frame.loading.write().unwrap();
                    let frame_page_id = std::mem::replace(&mut *loading_guard, page_id);

                    dir.insert(page_id, w_hdl.frame.index);
                    drop(dir);

                    // remove from old dir if needed
                    // It is ok if threads find this page before we do this, because we are holding the
                    // loading lock, and once we release it they will see the new (to them unexpected)
                    // page_id and they'll retry
                    let mut old_dir = self.shard_dirs[shard_hash(frame_page_id)].lock().unwrap();
                    old_dir.remove(&frame_page_id);
                    drop(old_dir);

                    self.io_read(&mut w_hdl)?;

                    let r_hdl = self.pin_downgrade(w_hdl);
                    drop(loading_guard);
                    return Ok(r_hdl);
                }
            }
        }
    }

    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_page_write(&self, page_id: u64, should_load: bool) -> Result<WrHdl<'_>, PagerErr> {
        let mut dir = self.shard_dirs[shard_hash(page_id)].lock().unwrap();

        match dir.get(&page_id) {
            Some(&frame_index) => {
                return Ok(self.pin_write(frame_index));
            }
            None => {
                let mut w_hdl = loop {
                    let free_frame_index = self.scan_for_eviction_candidate();
                    match self.try_pin_write(free_frame_index) {
                        None => continue,
                        Some(w_hdl) => break w_hdl,
                    }
                };

                let mut loading_guard = w_hdl.frame.loading.write().unwrap();
                let frame_page_id = std::mem::replace(&mut *loading_guard, page_id);

                dir.insert(page_id, w_hdl.frame.index);
                drop(dir);

                let mut old_dir = self.shard_dirs[shard_hash(frame_page_id)].lock().unwrap();
                old_dir.remove(&frame_page_id);
                drop(old_dir);

                if should_load {
                    self.io_read(&mut w_hdl)?;
                }

                return Ok(w_hdl);
            }
        };
    }

    #[must_use = "RAII WrHdl releases when dropped"]
    fn get_frame_write(&self, frame_index: usize) -> WrHdl<'_> {
        self.try_pin_write(frame_index).expect("must be uncontested")
    }

    #[must_use = "RAII ReadTxHdl releases when dropped"]
    pub(super) fn read_tx<'tx>(&'tx self) -> ReadTxHdl<'tx> {
        let superblock = {
            // we need to hold this guard while we put our value in the registry
            let curr_guard = self.current.read().expect("todo");
            let current = curr_guard.clone();

            let tx_id = current.tx_id.get();
            thread_local_tx_registry::register(tx_id);

            current
        };

        ReadTxHdl { pager: self, superblock }
    }

    #[must_use = "RAII WriteTxHdl releases when dropped"]
    pub(super) fn write_tx<'tx>(&'tx self) -> WriteTxHdl<'tx> {
        let lock = self.write_lock.lock().unwrap();

        let mut superblock = self.current.read().expect("todo").clone();
        let prev_page_id = superblock.page_id.get();
        superblock.tx_id += 1;
        superblock.page_id.set((prev_page_id + 1) % 2);

        WriteTxHdl {
            pager: self,
            _lock: lock,
            inner: RefCell::new(WriteTxHdlInner { superblock, created_pages: HashMap::new() }),
        }
    }
}

// -------------------------------------------------------------------------------------------------
// *            Frame Definitions                                                                  *
// -------------------------------------------------------------------------------------------------

impl FrameBuffer {
    #[must_use]
    fn zeros() -> Self {
        Self(UnsafeCell::new([0; PAGE_SIZE]))
    }
}

#[repr(align(64))]
struct FrameHeader {
    index:   usize,
    page_id: UnsafeCell<u64>, // TODO
    /// Negative is write, positive is read - write is exclusive
    pins:    AtomicI64,
    usage:   AtomicU64,
    loading: RwLock<u64>,
}

impl FrameHeader {
    fn new(index: usize) -> Self {
        Self {
            index:   index,
            page_id: PAGE_ID_NULL.into(),
            pins:    0.into(),
            usage:   0.into(),
            loading: RwLock::new(PAGE_ID_NULL),
        }
    }
}

// ------------ WrHdl ------------------------------------------------------------------------------

/// Exclusive frame write-handle
#[repr(align(64))]
pub(super) struct WrHdl<'pager> {
    pub(super) buf: &'pager mut [u8; PAGE_SIZE],
    pager:          &'pager Pager,
    frame:          &'pager FrameHeader,
    tx_id:          u64,
}

impl<'pager> WrHdl<'pager> {
    unsafe fn from_pager_index(pager: &'pager Pager, index: usize, tx_id: u64) -> Self {
        let frame = &pager.frames[index];
        let buf = unsafe { &mut *pager.pages[index].0.get() };
        Self { pager: pager, frame: frame, buf: buf, tx_id }
    }

    pub(super) fn flush(&mut self) -> Result<(), PagerErr> {
        self.pager.io_write(self, self.tx_id)
    }

    pub(super) fn get_page_id(&self) -> u64 {
        *self
            .frame
            .loading
            .try_read()
            .expect("loading rwlock shouldnt be contested when we have a WrHdl")
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
#[repr(align(64))]
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

pub(super) trait PgRdr<'tx> {
    fn get_page_read(&self, page_id: u64) -> Result<RdHdl<'tx>, PagerErr>;
}

pub(super) trait PgAlloc<'tx> {
    fn get_page_alloc(&self) -> Result<WrHdl<'tx>, PagerErr>;
    fn get_page_write(&self, page_id: u64) -> Result<WrHdl<'tx>, PagerErr>;
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

impl<'tx> PgRdr<'tx> for ReadTxHdl<'tx> {
    fn get_page_read(&self, page_id: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_page_read(page_id)
    }
}

// ------------ WriteTx ----------------------------------------------------------------------------

pub(super) struct WriteTxHdl<'tx> {
    pager: &'tx Pager,
    inner: RefCell<WriteTxHdlInner>,
    _lock: MutexGuard<'tx, ()>,
}

struct WriteTxHdlInner {
    superblock:    SuperblockHeader,
    created_pages: HashMap<u64, usize>,
}

impl WriteTxHdl<'_> {
    pub(super) fn commit(self, durability: Durability) -> Result<(), PagerErr> {
        let inner = self.inner.borrow_mut();

        for &frame_index in inner.created_pages.values() {
            let mut w_hdl = self.pager.get_frame_write(frame_index);
            // TODO check durability
            self.pager.io_write(&mut w_hdl, inner.superblock.tx_id.get())?;
        }

        let sb_page_id = inner.superblock.page_id.get();
        let mut w_hdl = self.pager.get_page_write(sb_page_id, false)?;
        copy_superblock_to_page(w_hdl.buf, &inner.superblock);
        self.pager.io_write(&mut w_hdl, inner.superblock.tx_id.get())?;

        // these don't need to be atomic - we are holding _lock anyway
        *self.pager.current.write().unwrap() = inner.superblock.clone();
        self.pager.tx_id.store(inner.superblock.tx_id.get(), Ordering::Relaxed);

        Ok(())
    }
}

impl<'tx> PgRdr<'tx> for WriteTxHdl<'tx> {
    fn get_page_read(&self, page_id: u64) -> Result<RdHdl<'tx>, PagerErr> {
        self.pager.get_page_read(page_id)
    }
}

impl<'tx> PgAlloc<'tx> for WriteTxHdl<'tx> {
    /// Bump allocates - also adds page to our dirty-page linked list
    fn get_page_alloc(&self) -> Result<WrHdl<'tx>, PagerErr> {
        let mut inner = self.inner.borrow_mut();
        let page_id = inner.superblock.alloc_bump_next_id.get();
        inner.superblock.alloc_bump_next_id.add_assign(1);
        let w_hdl = self.pager.get_page_write(page_id, false)?;
        inner.created_pages.insert(page_id, w_hdl.get_frame_index());
        Ok(w_hdl)
    }

    /// should return a writeable new page, or a writeable copy of an existing page (depending on
    /// page_id)
    fn get_page_write(&self, page_id: u64) -> Result<WrHdl<'tx>, PagerErr> {
        if let Some(&index) = self.inner.borrow().created_pages.get(&page_id) {
            return Ok(self.pager.get_frame_write(index));
        }

        let old_r_hdl = self.get_page_read(page_id)?;
        let new_w_hdl = self.get_page_alloc()?;
        new_w_hdl.buf.copy_from_slice(old_r_hdl.buf);
        Ok(new_w_hdl)
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

// -------------------------------------------------------------------------------------------------
// *            Util                                                                               *
// -------------------------------------------------------------------------------------------------

/// Does not compute checksum
fn copy_superblock_to_page(buf: &mut [u8; PAGE_SIZE], sb_header: &SuperblockHeader) {
    buf.zero();
    sb_header.write_to_prefix(buf).unwrap();
}

const fn shard_hash(mut page_id: u64) -> usize {
    page_id ^= page_id >> 33;
    page_id = page_id.wrapping_mul(0xff51_afd7_ed55_8ccd);
    page_id ^= page_id >> 33;
    (page_id as usize) & (SHARD_CNT - 1)
}
