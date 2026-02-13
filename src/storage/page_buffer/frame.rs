use std::fmt::Debug;
use std::sync::atomic::AtomicU16;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

use parking_lot::RwLock;
use parking_lot::RwLockReadGuard;
use parking_lot::RwLockWriteGuard;

use super::memory_alloc::SlabBox;
use crate::storage::pages::PAGE_ID_NULL;
use crate::PAGE_SIZE;

#[repr(align(64))]
pub(crate) struct Frame {
    // both could be smaller but this is aligned-padded anyway
    pub(crate) page_id_hint: AtomicU64,

    pub(crate) usage: AtomicU32,
    pub(crate) pins: AtomicU16,

    pub(crate) inner: RwLock<FrameInner>,
}

impl Frame {
    pub(crate) const fn new(frame_index: usize, buffer_ptr: *mut u8) -> Self {
        Self {
            page_id_hint: AtomicU64::new(PAGE_ID_NULL),
            usage: AtomicU32::new(0),
            pins: AtomicU16::new(0),
            inner: RwLock::new(FrameInner { state: State::Uninitialized, buffer_ptr, frame_index }),
        }
    }
}

/// **Possible state transitions:**
/// TODO update
/// - Writing:      `Uninitialized -> Writteable -> Dirty -> WrittenOut`
/// - Read:         `Uninitialized -> ReadIn`
/// - Read Error:   `Uninitialized -> ReadErrored`
///
/// NOTE there is not "WriteError" state - we poison our page buffer if we have a write-out error
#[derive(PartialEq, Eq, Debug)]
enum State {
    Uninitialized,

    ReadIn(u64),
    ReadErrored(std::io::ErrorKind),

    Writeable(u64),
    Dirty(u64),
    WrittenOut(u64),
}

pub(crate) struct FrameInner {
    frame_index: usize,
    state: State,
    buffer_ptr: *mut u8,
}

impl Debug for FrameInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("FrameInner").field(&self.state).finish()
    }
}

impl FrameInner {
    pub(crate) const fn index(&self) -> usize {
        self.frame_index
    }

    /// TODO rename
    /// this signifies that the page should be in the directory
    /// This would be false if the frame is uninitialized or we had a read-error
    pub(crate) const fn has_valid_page(&self) -> Option<u64> {
        match self.state {
            // we don't check Writeable because that state should only exist when a FrameWriteGuard
            // exists pinning it and it hasnt been commited yet
            State::ReadIn(page_id) | State::Dirty(page_id) | State::WrittenOut(page_id) => Some(page_id),
            _ => None,
        }
    }

    /// sets new `page_id` and cleans up `dirty` and `io_err` (`false`, `none`)
    pub(crate) fn state_uninit_to_writeable(&mut self, page_id: u64) {
        match self.state {
            State::Uninitialized => self.state = State::Writeable(page_id),
            _ => panic!("set_read_in called on invalid frame state ({:?})", self.state),
        }
    }

    pub(crate) fn state_uninit_to_read(&mut self, page_id: u64, res: Result<(), std::io::ErrorKind>) {
        if let State::Uninitialized = self.state {
            match res {
                Ok(()) => self.state = State::ReadIn(page_id),
                Err(err) => self.state = State::ReadErrored(err),
            }
        } else {
            panic!("set_read_result called on invalid frame state ({:?})", self.state);
        }
    }

    /// Reinitializes the page, signifying we do NOT have a page associated with this frame.
    /// Should only panic on dirty - we are trying to reinitialize a frame with data that
    /// hasnt been written out yet!
    pub(crate) fn state_to_uninit(&mut self) {
        match self.state {
            State::Dirty(_) => panic!("uninit called on invalid frame state ({:?})", self.state),
            _ => self.state = State::Uninitialized,
        }
    }

    pub(crate) fn get_read_error(&self) -> Option<std::io::ErrorKind> {
        match self.state {
            State::ReadErrored(err) => Some(err),
            State::ReadIn(_) => None,
            _ => panic!("get_read_error called on invalid frame state ({:?})", self.state),
        }
    }

    pub(crate) fn state_writeable_to_dirty(&mut self) {
        // i dont think well every call this on a dirty frame
        if let State::Writeable(page_id) = self.state {
            self.state = State::Dirty(page_id);
        } else {
            panic!("tried to mark frame as dirty while it was in invalid state ({:?})", self.state);
        }
    }

    pub(crate) fn state_dirty_to_written(&mut self) {
        if let State::Dirty(page_id) = self.state {
            self.state = State::WrittenOut(page_id);
        } else {
            panic!("set_written_out called on invalid frame state ({:?})", self.state);
        }
    }

    pub(crate) fn get_page_id(&self) -> u64 {
        match self.has_valid_page() {
            Some(page_id) => page_id,
            None => panic!("tried to get page_id from invalid frame state ({:?})", self.state),
        }
    }

    pub(crate) const fn is_dirty(&self) -> bool {
        matches!(self.state, State::Dirty(_))
    }
}

pub(crate) struct FrameReadGuard<'a> {
    inner: RwLockReadGuard<'a, FrameInner>,
    slab: &'a FrameSlab,
    pub(crate) buffer: &'a [u8],
}

impl std::ops::Deref for FrameReadGuard<'_> {
    type Target = FrameInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl Drop for FrameReadGuard<'_> {
    fn drop(&mut self) {
        self.slab.unpin(self.frame_index);
    }
}

/// NOTE `FrameWriteGuard` must be explicitly dropped using `cancel` or `commit`
pub(crate) struct FrameWriteGuard<'a> {
    inner: RwLockWriteGuard<'a, FrameInner>,
    slab: &'a FrameSlab,
    pub(crate) buffer: &'a mut [u8],
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
        self.slab.unpin(self.frame_index);
    }
}

/// A slab of frame slots backed by a single mmap allocation. Each slot is laid out as:
/// Frames are all stored contiguously, and buffers are asll stored contiguously (so that the
/// buffers can be page aligned)
/// The slot size is rounded up to the nearest 64-byte boundary so that every frame header
/// remains 64-byte aligned.
pub(super) struct FrameSlab {
    frames: Box<[Frame]>,
    page_slab: SlabBox<[u8]>,
}

// SAFETY
// the slab is owned by FrameSlab which coordinates access via Frame's RWLocks
unsafe impl Send for FrameSlab {}
unsafe impl Sync for FrameSlab {}

impl FrameSlab {
    pub(super) fn new(frame_count: usize) -> Self {
        let page_slab_size = frame_count * PAGE_SIZE as usize;
        let page_slab = SlabBox::<[u8]>::new_raw(page_slab_size);

        let frames = (0..frame_count)
            .map(|index| Frame::new(index, unsafe { page_slab.as_ptr().add(index * PAGE_SIZE as usize) }))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        tracing::debug!(
            "FrameSlab allocated {} - {} headers and {} pages",
            monke::fmt_size(page_slab_size),
            monke::fmt_size(frame_count * size_of::<Frame>()),
            monke::fmt_size(page_slab_size + frame_count * size_of::<Frame>()),
        );

        Self { page_slab, frames }
    }

    pub(crate) fn len(&self) -> usize {
        self.frames.len()
    }

    pub(crate) fn pin_count(&self, index: usize, ordering: Ordering) -> u16 {
        self.frames[index].pins.load(ordering)
    }

    fn unpin(&self, index: usize) {
        self.frames[index].pins.fetch_sub(1, Ordering::Release);
    }

    pub(super) fn downgrade_write_guard<'a>(&'a self, guard: FrameWriteGuard<'a>) -> FrameReadGuard<'a> {
        // returned `FrameReadGuard` takes over the pin.
        let guard = std::mem::ManuallyDrop::new(guard);
        // SAFETY: guard is inside ManuallyDrop so its Drop will never run; we take ownership
        // of `inner` here and it will be managed by the returned FrameReadGuard.
        let inner = unsafe { std::ptr::read(&guard.inner) };
        let downgraded = parking_lot::lock_api::RwLockWriteGuard::downgrade(inner);
        let buffer = unsafe { std::slice::from_raw_parts(downgraded.buffer_ptr.cast_const(), PAGE_SIZE as usize) };
        FrameReadGuard { inner: downgraded, buffer, slab: self }
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(super) fn pin_read(&self, index: usize) -> FrameReadGuard<'_> {
        self.frames[index].pins.fetch_add(1, Ordering::Release);
        self.frames[index].usage.fetch_add(1, Ordering::Relaxed);
        let guard = self.frames[index].inner.read();
        // SAFETY
        // we hold a read lock on frame.inner for the duration of the returned guard
        let buffer = unsafe { std::slice::from_raw_parts(guard.buffer_ptr.cast_const(), PAGE_SIZE as usize) };
        FrameReadGuard { inner: guard, buffer, slab: self }
    }

    #[must_use = "RAII FrameRef unpins when dropped"]
    pub(super) fn pin_write(&self, index: usize) -> FrameWriteGuard<'_> {
        self.frames[index].pins.fetch_add(1, Ordering::Release);
        self.frames[index].usage.fetch_add(1, Ordering::Relaxed);
        let guard = self.frames[index].inner.try_write().expect(
            "Frame write lock was contented - shouldn't happen. \
                Only a single thread should ever be even trying to write to a frame, because of CoW invarients",
        );
        // SAFETY
        // we hold an exclusive write lock on frame.inner for the duration of the returned guard,
        // ensuring no other guard can read/write the buffer simultaneously
        let buffer = unsafe { std::slice::from_raw_parts_mut(guard.buffer_ptr.cast(), PAGE_SIZE as usize) };
        FrameWriteGuard { inner: guard, buffer, slab: self, committed: false }
    }
}

impl std::ops::Index<usize> for FrameSlab {
    type Output = Frame;
    fn index(&self, index: usize) -> &Frame {
        assert!(index < self.frames.len(), "frame index out of bounds (index={}, len={})", index, self.frames.len());
        &self.frames[index]
    }
}
