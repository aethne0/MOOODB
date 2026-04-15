//! frame.rs
//!
//! implementation of frames, the overall memory buffer pool and the
//! lifetime/state-machine logic of frames.

use std::fmt::Debug;
use std::marker::PhantomData;

use super::PAGE_ID_NULL;
use super::PAGE_SIZE;
use super::StorageError;
use super::slab::SlabBox;
use crate::sync::*;

#[repr(align(64))]
pub(crate) struct Frame {
    pub(crate) index:        usize,
    pub(crate) page_id_hint: AtomicU64,
    pub(crate) inner:        RwLock<FrameInner>,
    pub(crate) usage:        AtomicU32,
    pub(crate) pins:         AtomicU16,
}

impl Frame {
    #[cfg_attr(not(loom), allow(clippy::missing_const_for_fn))]
    pub(crate) fn new(frame_index: usize) -> Self {
        Self {
            index:        frame_index,
            page_id_hint: AtomicU64::new(PAGE_ID_NULL),
            usage:        AtomicU32::new(0),
            pins:         AtomicU16::new(0),
            inner:        RwLock::new(FrameInner { state: State::Uninitialized }),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum State {
    Uninitialized,
    LoadPending(u64),
    Resident(u64),
    ReadErrored(u64, StorageError),
    Writeable(u64),
    Dirty(u64),
    Poisoned,
}

pub(crate) struct FrameInner {
    state: State,
}

impl FrameInner {
    pub(super) fn is_dirty(&self) -> Option<u64> {
        // TODO further narrow
        match self.state {
            State::Dirty(page_id) => Some(page_id),
            _ => None,
        }
    }
}

impl Debug for FrameInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("FrameInner").field(&self.state).finish()
    }
}

struct PinDropper<'a> {
    slab:  &'a FrameSlab,
    index: usize,
}

impl<'a> Drop for PinDropper<'a> {
    fn drop(&mut self) {
        self.slab.unpin(self.index);
    }
}

// -------------------------------------------------------------------------------------------------
// *            Guards                                                                             *
// -------------------------------------------------------------------------------------------------

/// This is a frame that has previously had data loaded into it for reading. We should be getting aa
pub(crate) struct Resident;
/// This is a Write
pub(crate) struct LoadPending;
pub(crate) struct Uninit;
pub(crate) struct Writeable;
pub(crate) struct Dirty;

pub(crate) trait WriteGuardState {}
impl WriteGuardState for Resident {}
impl WriteGuardState for LoadPending {}
impl WriteGuardState for Uninit {}
impl WriteGuardState for Writeable {}
impl WriteGuardState for Dirty {}

// -------------------------------------------------------------------------------------------------
// *            FrameReadGuard                                                                     *
// -------------------------------------------------------------------------------------------------

pub(crate) struct FrameReadGuard<'a> {
    pub(crate) index: usize,

    inner:       RwLockReadGuard<'a, FrameInner>,
    buffer:      &'a [u8; PAGE_SIZE],
    pin_dropper: Option<PinDropper<'a>>,
}

// ------------ Readable ---------------------------------------------------------------------------
impl<'a> FrameReadGuard<'a> {
    pub(crate) fn buffer(&self) -> &'a [u8; PAGE_SIZE] {
        self.buffer
    }
}

// -------------------------------------------------------------------------------------------------
// *            FrameWriteGuard                                                                    *
// -------------------------------------------------------------------------------------------------

/// NOTE `FrameWriteGuard` must be explicitly dropped using `cancel` or `commit`
pub(crate) struct FrameWriteGuard<'a, State>
where
    State: WriteGuardState,
{
    _phantom:         PhantomData<State>,
    pub(crate) index: usize,

    pub(crate) inner: RwLockWriteGuard<'a, FrameInner>,
    slab:             &'a FrameSlab,
    buffer:           &'a mut [u8; PAGE_SIZE],
    pin_dropper:      Option<PinDropper<'a>>,
}

impl<'a, Old: WriteGuardState> FrameWriteGuard<'a, Old> {
    fn transition<New: WriteGuardState>(mut self) -> FrameWriteGuard<'a, New> {
        FrameWriteGuard {
            _phantom:    PhantomData,
            index:       self.index,
            slab:        self.slab,
            inner:       self.inner,
            buffer:      self.buffer,
            pin_dropper: self.pin_dropper.take(),
        }
    }
}

// ------------ Uninit -----------------------------------------------------------------------------
impl<'a> FrameWriteGuard<'a, Uninit> {
    pub(crate) fn abandon(self) {
        assert!(matches!(self.inner.state, State::Uninitialized));
    }

    pub(crate) fn buffer<'b>(&'b mut self) -> &'b mut [u8; PAGE_SIZE] {
        self.buffer
    }

    pub(crate) fn mark_load_pending(mut self, page_id: u64) -> FrameWriteGuard<'a, LoadPending> {
        match self.inner.state {
            State::Uninitialized => self.inner.state = State::LoadPending(page_id),
            _ => unreachable!(),
        }
        Self::transition(self)
    }

    pub(crate) fn mark_writeable(mut self, page_id: u64) -> FrameWriteGuard<'a, Writeable> {
        match self.inner.state {
            State::Uninitialized => self.inner.state = State::Writeable(page_id),
            _ => unreachable!(),
        }
        Self::transition(self)
    }
}

// ------------ Writeable --------------------------------------------------------------------------
impl<'a> FrameWriteGuard<'a, Writeable> {
    pub(crate) fn abandon(mut self) {
        match self.inner.state {
            State::Writeable(page_id) => self.inner.state = State::Resident(page_id),
            _ => unreachable!(),
        }
    }

    pub(crate) fn commit(mut self) -> FrameWriteGuard<'a, Dirty> {
        match self.inner.state {
            State::Writeable(page_id) => self.inner.state = State::Dirty(page_id),
            _ => unreachable!(),
        }
        Self::transition(self)
    }

    pub(crate) fn buffer<'b>(&'b mut self) -> &'b mut [u8; PAGE_SIZE] {
        self.buffer
    }

    pub(crate) fn buffer_ref<'b>(&'b self) -> &'b [u8; PAGE_SIZE] {
        self.buffer
    }
}

// ------------ Readable ---------------------------------------------------------------------------
impl<'a> FrameWriteGuard<'a, Resident> {
    pub(crate) fn abandon(self) {
        match self.inner.state {
            State::Resident(_) => {}
            _ => unreachable!(),
        }
    }

    pub(crate) fn page_id(&self) -> u64 {
        match self.inner.state {
            State::Resident(page_id) => {
                assert!(page_id != PAGE_ID_NULL);
                page_id
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn mark_evicted(mut self) -> FrameWriteGuard<'a, Uninit> {
        match self.inner.state {
            State::Resident(_) => self.inner.state = State::Uninitialized,
            _ => unreachable!(),
        }
        Self::transition(self)
    }
}

// ------------ LoadPending ------------------------------------------------------------------------
impl<'a> FrameWriteGuard<'a, LoadPending> {
    pub(crate) fn buffer<'b>(&'b mut self) -> &'b mut [u8; PAGE_SIZE] {
        self.buffer
    }

    pub(crate) fn page_id(&self) -> u64 {
        match self.inner.state {
            State::LoadPending(page_id) => {
                assert!(page_id != PAGE_ID_NULL);
                page_id
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn mark_load_ok(mut self) -> FrameReadGuard<'a> {
        match self.inner.state {
            State::LoadPending(page_id) => {
                self.inner.state = State::Resident(page_id);
                self.slab.downgrade_guard(self)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn mark_load_err(mut self, err: StorageError) {
        match self.inner.state {
            State::LoadPending(page_id) => {
                self.inner.state = State::ReadErrored(page_id, err);
            }
            _ => unreachable!(),
        }
    }
}

// ------------ Dirty ------------------------------------------------------------------------------
impl<'a> FrameWriteGuard<'a, Dirty> {
    pub(crate) fn buffer<'b>(&'b mut self) -> &'b mut [u8; PAGE_SIZE] {
        self.buffer
    }

    pub(crate) fn abandon(self) {
        match self.inner.state {
            State::Dirty(_) => {}
            _ => unreachable!(),
        }
    }

    pub(crate) fn page_id(&self) -> u64 {
        match self.inner.state {
            State::Dirty(page_id) => {
                assert!(page_id != PAGE_ID_NULL);
                page_id
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn mark_poisoned(mut self) {
        match self.inner.state {
            State::Dirty(_) => {
                self.slab.poison(self.index);
                self.inner.state = State::Poisoned
            }
            _ => unreachable!(),
        }
    }

    /// for eviction
    pub(crate) fn mark_written_out_and_reinit(mut self) -> FrameWriteGuard<'a, Uninit> {
        match self.inner.state {
            State::Dirty(_) => self.inner.state = State::Uninitialized,
            _ => unreachable!(),
        }
        Self::transition(self)
    }

    /// turns it into a readable frame - use this if you are not trying to evict
    pub(crate) fn mark_written_out(mut self) -> FrameWriteGuard<'a, Resident> {
        match self.inner.state {
            State::Dirty(page_id) => self.inner.state = State::Resident(page_id),
            _ => unreachable!(),
        }
        Self::transition(self)
    }
}
// -------------------------------------------------------------------------------------------------
// *            FrameSlab                                                                          *
// -------------------------------------------------------------------------------------------------
/// A slab of frame slots backed by a single mmap allocation. Each slot is laid out as:
/// Frames are all stored contiguously, and buffers are asll stored contiguously (so that the
/// buffers can be page aligned)
/// The slot size is rounded up to the nearest 64-byte boundary so that every frame header
/// remains 64-byte aligned.
pub(super) struct FrameSlab {
    frames:    Box<[Frame]>,
    page_slab: SlabBox,
}

// SAFETY
// the slab is owned by FrameSlab which coordinates access via Frame's RWLocks
unsafe impl Send for FrameSlab {}
unsafe impl Sync for FrameSlab {}

pub(crate) enum PinWrite<'a> {
    CasFail,
    Uninit(FrameWriteGuard<'a, Uninit>),
    ResidentReadable(FrameWriteGuard<'a, Resident>),
    ResidentDirty(FrameWriteGuard<'a, Dirty>),
}

impl<'a> PinWrite<'a> {
    pub(crate) fn abandon(self) {
        match self {
            PinWrite::CasFail => {}
            PinWrite::ResidentDirty(g) => g.abandon(),
            PinWrite::Uninit(g) => g.abandon(),
            PinWrite::ResidentReadable(g) => g.abandon(),
        }
    }
}

impl FrameSlab {
    pub(super) fn new(frame_count: usize) -> Self {
        let page_slab_size = frame_count * PAGE_SIZE;
        let page_slab = SlabBox::new_raw(page_slab_size);

        let frames = (0..frame_count)
            .map(|frame_index| Frame::new(frame_index))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        Self { page_slab, frames }
    }

    pub(crate) const fn frame_count(&self) -> usize {
        self.frames.len()
    }

    pub(crate) fn pin_count(&self, index: usize) -> u16 {
        self.frames[index].pins.load(Ordering::Acquire)
    }

    /// leaks a pin so this frame wont get evicted
    /// Might make this do something different later - somewhat documentational
    fn poison(&self, index: usize) {
        self.frames[index].pins.fetch_add(1, Ordering::Release);
    }

    fn unpin(&self, index: usize) {
        let prev = self.frames[index].pins.fetch_sub(1, Ordering::Release);
        assert!(prev > 0, "unpin underflow!");
    }

    /// NOTE this does not affect state
    fn downgrade_guard<'a>(
        &'a self, mut guard: FrameWriteGuard<'a, LoadPending>,
    ) -> FrameReadGuard<'a> {
        assert!(matches!(guard.inner.state, State::Resident(_)));
        let index = guard.index;

        // take our new pin before releasing the old one
        let pin_dropper = guard.pin_dropper.take();

        drop(guard);
        let guard = self.frames[index].inner.read().unwrap();

        // SAFETY
        // we hold a read lock on frame.inner for the duration of the returned guard
        let buffer: &[u8; PAGE_SIZE] =
            unsafe { &*(self.page_slab.as_ptr().add(PAGE_SIZE * index) as *const [u8; PAGE_SIZE]) };

        FrameReadGuard { index, buffer, inner: guard, pin_dropper }
    }

    /// NOTE this does not affect state
    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(super) fn pin_read(&self, index: usize) -> Result<FrameReadGuard<'_>, StorageError> {
        self.frames[index].pins.fetch_add(1, Ordering::Release);
        self.frames[index].usage.fetch_add(1, Ordering::Relaxed);
        let guard = self.frames[index].inner.read().unwrap();
        // SAFETY
        // we hold a read lock on frame.inner for the duration of the returned guard

        let buffer: &[u8; PAGE_SIZE] =
            unsafe { &*(self.page_slab.as_ptr().add(PAGE_SIZE * index) as *const [u8; PAGE_SIZE]) };

        match guard.state {
            State::Resident(_) | State::Dirty(_) => Ok(FrameReadGuard {
                index,
                buffer,
                inner: guard,
                pin_dropper: Some(PinDropper { slab: self, index }),
            }),
            State::ReadErrored(_, err) => Err(err),
            _ => {
                unreachable!(
                    "tried to get read guard on frame while it was in an \
                    invalid state (frame was {:?})",
                    guard.state
                );
            }
        }
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(crate) fn pin_write<'a>(&'a self, index: usize) -> PinWrite<'a> {
        if self.frames[index]
            .pins
            .compare_exchange(0, 1, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return PinWrite::CasFail;
        }

        self.frames[index].usage.fetch_add(1, Ordering::Relaxed);
        let guard = self.frames[index].inner.write().unwrap();
        // SAFETY
        // we hold an exclusive write lock on frame.inner for the duration of the returned guard,
        // ensuring no other guard can read/write the buffer simultaneously

        let buffer: &mut [u8; PAGE_SIZE] = unsafe {
            &mut *(self.page_slab.as_ptr().add(PAGE_SIZE * index) as *mut [u8; PAGE_SIZE])
        };

        let state = guard.state;
        let fwg = FrameWriteGuard {
            index,
            slab: self,
            buffer,
            inner: guard,
            pin_dropper: Some(PinDropper { slab: self, index }),
            _phantom: PhantomData,
        };

        match state {
            State::Uninitialized => PinWrite::Uninit(fwg),
            State::ReadErrored(_, _) => PinWrite::Uninit(fwg),
            State::Resident(_) => PinWrite::ResidentReadable(FrameWriteGuard::transition(fwg)),
            State::Dirty(_) => PinWrite::ResidentDirty(FrameWriteGuard::transition(fwg)),

            State::Poisoned => {
                unreachable!(
                    "poisoned frame should be pin-leaked, it shouldnt be an eviction \
                    canadidate"
                )
            }
            State::Writeable(_) => unreachable!(
                "frames that are writeable either need to be written or abandoned before being \
                unpinned / dropped"
            ),
            State::LoadPending(_) => unreachable!(
                "frames that are load-pending either need to be written or abandoned before being \
                unpinned / dropped"
            ),
        }
    }
}

impl std::ops::Index<usize> for FrameSlab {
    type Output = Frame;
    fn index(&self, index: usize) -> &Frame {
        assert!(
            index < self.frames.len(),
            "frame index out of bounds (index={}, len={})",
            index,
            self.frames.len()
        );
        &self.frames[index]
    }
}
