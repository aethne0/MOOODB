//! Sync primitive shim — selects the right implementation based on the active
//! testing harness:
//!
//! | Build flag          | Source   | How to activate                          |
//! |---------------------|----------|------------------------------------------|
//! | `--cfg loom`        | loom     | `RUSTFLAGS="--cfg loom" cargo test`      |
//! | `--cfg shuttle`     | shuttle  | `RUSTFLAGS="--cfg shuttle" cargo test`   |
//! | *(neither)*         | std      | normal builds / tests                    |
//!
//! Import from here instead of `std::sync` so that loom/shuttle can intercept
//! all synchronisation points during model-checking runs.

// ── loom ─────────────────────────────────────────────────────────────────────

#[cfg(loom)]
#[allow(unused_imports)]
mod imp {
    pub(crate) use loom::cell::UnsafeCell;
    pub(crate) use loom::sync::{
        Arc, Condvar, Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
    };
    pub(crate) use loom::sync::atomic::{
        AtomicBool, AtomicI32, AtomicI64, AtomicU16, AtomicU32, AtomicU64, AtomicUsize, Ordering,
    };

    pub(crate) mod thread {
        // loom does not implement thread::scope — scoped threads would bypass
        // loom's scheduler entirely, so scope is intentionally absent here.
        pub(crate) use loom::thread::{spawn, yield_now, JoinHandle};
    }
}

// ── shuttle ───────────────────────────────────────────────────────────────────

#[cfg(all(shuttle, not(loom)))]
#[allow(unused_imports)]
mod imp {
    pub(crate) use std::cell::UnsafeCell;
    pub(crate) use shuttle::sync::{
        Arc, Condvar, Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
    };
    pub(crate) use shuttle::sync::atomic::{
        AtomicBool, AtomicI32, AtomicI64, AtomicU16, AtomicU32, AtomicU64, AtomicUsize, Ordering,
    };

    pub(crate) mod thread {
        pub(crate) use shuttle::thread::{scope, spawn, yield_now, JoinHandle, Scope, ScopedJoinHandle};
    }
}

// ── std ───────────────────────────────────────────────────────────────────────

#[cfg(not(any(loom, shuttle)))]
#[allow(unused_imports)]
mod imp {
    pub(crate) use std::cell::UnsafeCell;
    pub(crate) use std::sync::{
        Arc, Condvar, Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
    };
    pub(crate) use std::sync::atomic::{
        AtomicBool, AtomicI32, AtomicI64, AtomicU16, AtomicU32, AtomicU64, AtomicUsize, Ordering,
    };

    pub(crate) mod thread {
        pub(crate) use std::thread::{scope, spawn, yield_now, JoinHandle, Scope, ScopedJoinHandle};
    }
}

#[allow(unused_imports)]
pub(crate) use imp::*;
