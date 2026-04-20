// --- shuttle ---

#[cfg(all(shuttle, not(loom)))]
#[allow(unused_imports)]
mod imp {
    pub(crate) use shuttle::sync::Arc;
    pub(crate) use shuttle::sync::Condvar;
    pub(crate) use shuttle::sync::Mutex;
    pub(crate) use shuttle::sync::MutexGuard;
    pub(crate) use shuttle::sync::RwLock;
    pub(crate) use shuttle::sync::RwLockReadGuard;
    pub(crate) use shuttle::sync::RwLockWriteGuard;
    pub(crate) use shuttle::sync::atomic::AtomicBool;
    pub(crate) use shuttle::sync::atomic::AtomicI32;
    pub(crate) use shuttle::sync::atomic::AtomicI64;
    pub(crate) use shuttle::sync::atomic::AtomicU16;
    pub(crate) use shuttle::sync::atomic::AtomicU32;
    pub(crate) use shuttle::sync::atomic::AtomicU64;
    pub(crate) use shuttle::sync::atomic::AtomicUsize;
    pub(crate) use shuttle::sync::atomic::Ordering;
    pub(crate) use std::cell::UnsafeCell;

    pub(crate) mod thread {
        pub(crate) use shuttle::thread::JoinHandle;
        pub(crate) use shuttle::thread::Scope;
        pub(crate) use shuttle::thread::ScopedJoinHandle;
        pub(crate) use shuttle::thread::scope;
        pub(crate) use shuttle::thread::spawn;
        pub(crate) use shuttle::thread::yield_now;
    }
}

// --- std ---

#[cfg(not(any(loom, shuttle)))]
#[allow(unused_imports)]
mod imp {
    pub(crate) use std::cell::UnsafeCell;
    pub(crate) use std::sync::Arc;
    pub(crate) use std::sync::Condvar;
    pub(crate) use std::sync::Mutex;
    pub(crate) use std::sync::MutexGuard;
    pub(crate) use std::sync::RwLock;
    pub(crate) use std::sync::RwLockReadGuard;
    pub(crate) use std::sync::RwLockWriteGuard;
    pub(crate) use std::sync::atomic::AtomicBool;
    pub(crate) use std::sync::atomic::AtomicI32;
    pub(crate) use std::sync::atomic::AtomicI64;
    pub(crate) use std::sync::atomic::AtomicU16;
    pub(crate) use std::sync::atomic::AtomicU32;
    pub(crate) use std::sync::atomic::AtomicU64;
    pub(crate) use std::sync::atomic::AtomicUsize;
    pub(crate) use std::sync::atomic::Ordering;

    pub(crate) mod thread {
        pub(crate) use std::thread::JoinHandle;
        pub(crate) use std::thread::Scope;
        pub(crate) use std::thread::ScopedJoinHandle;
        pub(crate) use std::thread::scope;
        pub(crate) use std::thread::spawn;
        pub(crate) use std::thread::yield_now;
    }
}

#[allow(unused_imports)]
pub(crate) use imp::*;
