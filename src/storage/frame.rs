use std::fmt::Debug;

use super::slab::SlabBox;
use super::StorageError;
use super::PAGE_ID_NULL;
use super::PAGE_SIZE;
use crate::sync::*;

#[repr(align(64))]
pub(crate) struct Frame {
    // both could be smaller but this is aligned-padded anyway
    pub(crate) index: usize,
    pub(crate) page_id_hint: AtomicU64,
    pub(crate) inner: RwLock<FrameInner>,
    pub(crate) usage: AtomicU32,
    pub(crate) pins: AtomicU16,
}

impl Frame {
    // loom's atomic and lock types are not const-initializable, so we drop `const` under loom.
    #[cfg_attr(not(loom), allow(clippy::missing_const_for_fn))]
    pub(crate) fn new(frame_index: usize) -> Self {
        Self {
            index: frame_index,
            page_id_hint: AtomicU64::new(PAGE_ID_NULL),
            usage: AtomicU32::new(0),
            pins: AtomicU16::new(0),
            inner: RwLock::new(FrameInner { state: State::Uninitialized }),
        }
    }
}

/// **Possible state transitions:**
/// TODO update
/// - Writing:      `Uninitialized -> Writteable -> Dirty -> WrittenOut`
/// - Read:         `Uninitialized -> ReadPending`
/// - Read:         `ReadPending   -> ReadIn`
/// - Read Error:   `ReadPending   -> ReadErrored`
///
/// NOTE there is not "WriteError" state - we poison our page buffer if we have a write-out error
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum State {
    Uninitialized,

    ReadPending(u64),
    ReadSuccessful(u64),
    ReadErrored(u64, StorageError),

    Writeable(u64),
    Dirty(u64),
    WrittenOut(u64),
}

pub(crate) struct FrameInner {
    state: State,
}

impl FrameInner {
    pub(super) fn state_to_uninit(&mut self) {
        if matches!(self.state, State::Dirty(_)) {
            unreachable!("invalid frame state transition (frame was {:?})", self.state);
        }
        self.state = State::Uninitialized;
    }

    pub(super) fn state_uninit_to_readpending(&mut self, page_id: u64) {
        if !matches!(self.state, State::Uninitialized) {
            unreachable!("invalid frame state transition (frame was {:?})", self.state);
        }
        self.state = State::ReadPending(page_id);
    }

    pub(super) fn state_readpending_to_read(&mut self, err: Option<StorageError>) {
        match self.state {
            State::ReadPending(page_id) => {
                self.state = match err {
                    Some(err) => State::ReadErrored(page_id, err),
                    None => State::ReadSuccessful(page_id),
                }
            }
            _ => unreachable!("invalid frame state transition (frame was {:?})", self.state),
        }
    }

    pub(super) fn state_uninit_to_writeable(&mut self, page_id: u64) {
        if !matches!(self.state, State::Uninitialized) {
            unreachable!("invalid frame state transition (frame was {:?})", self.state);
        }
        self.state = State::Writeable(page_id);
    }

    pub(super) fn state_writeable_to_dirty(&mut self) {
        match self.state {
            State::Writeable(page_id) => self.state = State::Dirty(page_id),
            _ => unreachable!("invalid frame state transition (frame was {:?})", self.state),
        }
    }

    pub(super) fn state_dirty_to_writtenout(&mut self) {
        match self.state {
            State::Dirty(page_id) => self.state = State::WrittenOut(page_id),
            _ => unreachable!("invalid frame state transition (frame was {:?})", self.state),
        }
    }

    pub(crate) fn has_read_error(&self) -> Option<StorageError> {
        match self.state {
            State::ReadSuccessful(_) => None,
            State::ReadErrored(_, err) => Some(err),
            _ => unreachable!("invalid frame state transition (frame was {:?})", self.state),
        }
    }

    pub(super) fn has_page(&self) -> Option<u64> {
        // TODO further narrow
        match self.state {
            State::ReadPending(page_id) => Some(page_id),
            State::ReadSuccessful(page_id) => Some(page_id),
            State::ReadErrored(page_id, _) => Some(page_id),
            State::Dirty(page_id) => Some(page_id),
            State::Writeable(page_id) => Some(page_id),
            State::WrittenOut(page_id) => Some(page_id),
            _ => None,
        }
    }

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

pub(crate) struct FrameReadGuard<'a> {
    pub(crate) index: usize,
    inner: RwLockReadGuard<'a, FrameInner>,
    slab: &'a FrameSlab,
    pub(crate) buffer: &'a [u8; PAGE_SIZE],
}

impl std::ops::Deref for FrameReadGuard<'_> {
    type Target = FrameInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl Drop for FrameReadGuard<'_> {
    fn drop(&mut self) {
        self.slab.unpin(self.index);
    }
}

/// NOTE `FrameWriteGuard` must be explicitly dropped using `cancel` or `commit`
pub(crate) struct FrameWriteGuard<'a> {
    pub(crate) index: usize,
    inner: RwLockWriteGuard<'a, FrameInner>,
    slab: &'a FrameSlab,
    pub(crate) buffer: &'a mut [u8; PAGE_SIZE],
    committed: bool,
}

impl FrameWriteGuard<'_> {
    /// Consumes guard and sets frame back to uninitialized. Must not be called on a Dirty frame.
    pub(crate) fn cancel(mut self) {
        debug_assert!(
            !matches!(self.state, State::Dirty(_)),
            "FrameWriteGuard cancelled while dirty — uncommitted data would be lost"
        );
        self.committed = true;
        self.inner.state_to_uninit();
    }

    /// Releases the guard without changing frame state. For use in eviction when bailing out
    /// after discovering the frame is contended or the shard hint was stale.
    pub(super) fn release(mut self) {
        self.committed = true;
        // drop releases the write lock and unpins
    }

    /// Consumes guard and sets frame to dirty, marking it for write-out. Must be in Writeable state.
    pub(crate) fn commit(mut self) {
        debug_assert!(matches!(self.state, State::Writeable(_)), "FrameWriteGuard dropped in weird state");
        self.committed = true;
        self.inner.state_writeable_to_dirty();
    }
}

impl std::ops::Deref for FrameWriteGuard<'_> {
    type Target = FrameInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl std::ops::DerefMut for FrameWriteGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl Drop for FrameWriteGuard<'_> {
    fn drop(&mut self) {
        debug_assert!(self.committed, "FrameWriteGuard::Drop called without it being `commit`ed or `cancelled`");
        self.slab.unpin(self.index);
    }
}

/// A slab of frame slots backed by a single mmap allocation. Each slot is laid out as:
/// Frames are all stored contiguously, and buffers are asll stored contiguously (so that the
/// buffers can be page aligned)
/// The slot size is rounded up to the nearest 64-byte boundary so that every frame header
/// remains 64-byte aligned.
pub(super) struct FrameSlab {
    frames: Box<[Frame]>,
    page_slab: SlabBox,
}

// SAFETY
// the slab is owned by FrameSlab which coordinates access via Frame's RWLocks
unsafe impl Send for FrameSlab {}
unsafe impl Sync for FrameSlab {}

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

    pub(crate) fn pin_count(&self, frame_index: usize) -> u16 {
        self.frames[frame_index].pins.load(Ordering::Acquire)
    }

    fn unpin(&self, frame_index: usize) {
        self.frames[frame_index].pins.fetch_sub(1, Ordering::Release);
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(super) fn pin_read(&self, index: usize) -> FrameReadGuard<'_> {
        self.frames[index].pins.fetch_add(1, Ordering::Release);
        self.frames[index].usage.fetch_add(1, Ordering::Relaxed);
        let guard = self.frames[index].inner.read().unwrap();
        // SAFETY
        // we hold a read lock on frame.inner for the duration of the returned guard

        let buffer: &[u8; PAGE_SIZE] =
            unsafe { &*(self.page_slab.as_ptr().add(PAGE_SIZE * index) as *const [u8; PAGE_SIZE]) };

        FrameReadGuard { index, inner: guard, buffer, slab: self }
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(super) fn pin_write(&self, index: usize) -> FrameWriteGuard<'_> {
        self.frames[index].pins.fetch_add(1, Ordering::Release);
        self.frames[index].usage.fetch_add(1, Ordering::Relaxed);
        let guard = self.frames[index].inner.write().unwrap();
        // SAFETY
        // we hold an exclusive write lock on frame.inner for the duration of the returned guard,
        // ensuring no other guard can read/write the buffer simultaneously

        let buffer: &mut [u8; PAGE_SIZE] =
            unsafe { &mut *(self.page_slab.as_ptr().add(PAGE_SIZE * index) as *mut [u8; PAGE_SIZE]) };

        FrameWriteGuard { index, slab: self, buffer, inner: guard, committed: false }
    }
}

impl std::ops::Index<usize> for FrameSlab {
    type Output = Frame;
    fn index(&self, index: usize) -> &Frame {
        assert!(index < self.frames.len(), "frame index out of bounds (index={}, len={})", index, self.frames.len());
        &self.frames[index]
    }
}
