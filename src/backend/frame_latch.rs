//! we will implement our own RWLock style frame-latch, because we need atomic downgrade which the
//! std rwlock does not provide. For now we are borrowing parking-lot's until we implement our own,
//! which provides atomic downgrade
pub(super) type Latch<T> = parking_lot::RwLock<T>;
pub(super) type LatchReadGuard<'a, T> = parking_lot::RwLockReadGuard<'a, T>;
pub(super) type LatchWriteGuard<'a, T> = parking_lot::RwLockWriteGuard<'a, T>;
pub(super) fn latch_downgrade<'a, T>(guard: LatchWriteGuard<'a, T>) -> LatchReadGuard<'a, T> {
    parking_lot::RwLockWriteGuard::downgrade(guard)
}
