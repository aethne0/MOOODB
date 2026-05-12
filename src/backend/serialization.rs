use std::fmt::Display;
use std::mem::offset_of;
use std::ops::AddAssign;

use super::pgid_valid;
use super::PAGE_SIZE;
use crate::mooo_assert;

// ------------ Common Page Header Prefix ----------------------------------------------------------

pub(crate) const PAGE_HEADER_SIZE: u16 = 0x40;
pub(crate) const END_OF_PAGE: u16 = PAGE_SIZE as u16 - 1;

/// The first 32 bytes of every page on disk, regardless of page type.
///
/// Layout (all big-endian):
/// ```text
/// offset  0 | checksum    u64
/// offset  8 | txid        u64
/// offset 16 | pgid        u64
/// offset 24 | pgtype      u64
/// ```
#[derive(Clone)]
#[repr(C)]
pub(crate) struct PagePrefix {
    pub(crate) checksum: SerializedU64,
    pub(crate) pgid:     SerializedU64,
    pub(crate) txid:     SerializedU64,
    pub(crate) pgtype:   SerializedU64,
}
unsafe impl Serialized for PagePrefix {}

/// Where to start checksumming, we want to compute checksum using only the bytes AFTER the
/// checksum, or else writing the checksum itself will invalidate itself.
pub(crate) const CHECKSUM_START_OFFSET: usize = offset_of!(PagePrefix, pgid);

impl PagePrefix {
    pub(crate) fn new(pgid: u64, checksum: u64, txid: u64, pgtype: SerializedU64) -> Self {
        Self {
            checksum: checksum.into(),
            pgid:     pgid.into(),
            txid:     txid.into(),
            pgtype:   pgtype,
        }
    }
}

// ------------ FreeEntry --------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(crate) struct FreeEntry {
    pub(crate) txid: SerializedU64,
    pub(crate) pgid: SerializedU48,
}

impl FreeEntry {
    pub(crate) fn new(txid: impl Into<SerializedU64>, pgid: impl Into<SerializedU48>) -> Self {
        Self { txid: txid.into(), pgid: pgid.into() }
    }

    // Gets minimum FreeEntry-key with this txid
    pub(crate) fn txid_bound(txid: impl Into<SerializedU64>) -> Self {
        Self { txid: txid.into(), pgid: 0.into() }
    }
}
unsafe impl Serialized for FreeEntry {}

// ------------ HeapPtr ----------------------------------------------------------------------------

/// most-significant 48 bits are pgid, lower are slot
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct HeapPtr(SerializedU64);
impl HeapPtr {
    pub(crate) fn new(pgid: u64, slot_index: u16) -> Self {
        mooo_assert!(pgid_valid(pgid));
        let val = (pgid << 16) | (slot_index as u64);
        Self(val.into())
    }

    pub(crate) fn set_pgid(&mut self, pgid: u64) {
        mooo_assert!(pgid_valid(pgid));
        self.0 = ((pgid << 16) | (self.0.get() & 0xffff)).into();
    }

    pub(crate) fn set_slot(&mut self, slot_index: u16) {
        self.0 = ((self.0.get() & 0xffff_ffff_ffff_0000) | (slot_index as u64)).into();
    }

    pub(crate) fn pgid(&self) -> u64 {
        (self.0.get() & 0xffff_ffff_ffff_0000) >> 16
    }

    pub(crate) fn slot(&self) -> u16 {
        (self.0.get() & 0xffff) as u16
    }
}
unsafe impl Serialized for HeapPtr {}
impl From<SerializedU64> for HeapPtr {
    fn from(value: SerializedU64) -> Self {
        HeapPtr(value)
    }
}
impl Into<SerializedU64> for HeapPtr {
    fn into(self) -> SerializedU64 {
        self.0
    }
}

// ▪   ▐ ▄ ▄▄▄▄▄▄▄▄ . ▄▄ • ▄▄▄ .▄▄▄
// ██ •█▌▐█•██  ▀▄.▀·▐█ ▀ ▪▀▄.▀·▀▄ █·
// ▐█·▐█▐▐▌ ▐█.▪▐▀▀▪▄▄█ ▀█▄▐▀▀▪▄▐▀▀▄
// ▐█▌██▐█▌ ▐█▌·▐█▄▄▌▐█▄▪▐█▐█▄▄▌▐█•█▌   Serialized Integer Types
// ▀▀▀▀▀ █▪ ▀▀▀  ▀▀▀ ·▀▀▀▀  ▀▀▀ .▀  ▀

/// A type that is serializable — lives on disk, cached pages, or network packets in serialized
/// form.
///
/// # Safety
///
/// Implementors must satisfy all of the following:
///
/// 1. **All bit patterns are valid.** `ref_from_bytes` and `mut_from_bytes` cast arbitrary bytes
///    directly to `&Self`/`&mut Self`, and `new_zeroed` produces an all-zeros instance. Types
///    with invalid bit patterns (enums, `bool`, `NonZero*`, references) must not implement this
///    trait.
///
/// 2. **No padding bytes.** `as_bytes` exposes the raw memory of `Self`. Padding bytes are
///    uninitialized in Rust; reading them is UB, and writing them to disk produces
///    nondeterministic output.
///
/// 3. **Alignment 1.** `ref_from_bytes` and `mut_from_bytes` cast `bytes.as_ptr()` directly to
///    `*const Self` with no alignment check. If `Self` has alignment > 1 and the slice is not
///    suitably aligned, that cast is UB.
///
/// 4. **No interior mutability.** `as_bytes` returns a shared `&[u8]` view of `self`. A type
///    containing `UnsafeCell` could be mutated through the original reference while that view
///    exists, violating aliasing rules.
///
/// 5. **`#[repr(C)]` or `#[repr(transparent)]`.** The in-memory layout must be stable and
///    well-defined so the byte representation is predictable across compilations.
///
/// ## Why the primitive serialized integer types satisfy this
///
/// `SerializedU64`, `SerializedU32`, `SerializedU16`, and `SerializedU48` are all
/// `#[repr(transparent)]` wrappers around `[u8; N]`. Byte arrays trivially satisfy every
/// requirement: every bit pattern is valid, there is no padding, alignment is 1, and there is
/// no `UnsafeCell`.
///
/// ## Why compound types (e.g. `PagePrefix`, `SuperblockHeader`) satisfy this
///
/// A `#[repr(C)]` struct whose fields are all `Serialized` types inherits all five properties.
/// `repr(C)` lays fields out in declaration order and inserts padding only to satisfy field
/// alignment requirements. Since every `Serialized` field has alignment 1, no inter-field
/// padding is ever inserted, so the struct has alignment 1 and no padding bytes. Bit-pattern
/// validity and the absence of interior mutability follow field-by-field from the fields
/// themselves.
pub(crate) unsafe trait Serialized: Sized {
    fn as_bytes(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self as *const Self as *const u8, size_of::<Self>()) }
    }

    fn ref_from_bytes(bytes: &[u8]) -> &Self {
        mooo_assert!(bytes.len() >= size_of::<Self>(), "buffer too small for type");
        unsafe { &*(bytes.as_ptr() as *const Self) }
    }

    fn mut_from_bytes(bytes: &mut [u8]) -> &mut Self {
        mooo_assert!(bytes.len() >= size_of::<Self>(), "buffer too small for type");
        unsafe { &mut *(bytes.as_mut_ptr() as *mut Self) }
    }

    fn read_from_bytes(bytes: &[u8]) -> Self
    where
        Self: Copy,
    {
        *Self::ref_from_bytes(bytes)
    }

    fn new_zeroed() -> Self {
        unsafe { std::mem::zeroed() }
    }

    fn write_to_prefix(&self, buf: &mut [u8]) {
        buf[..size_of::<Self>()].copy_from_slice(self.as_bytes());
    }

    fn mut_from_prefix(buf: &mut [u8]) -> &mut Self {
        Self::mut_from_bytes(&mut buf[..size_of::<Self>()])
    }
}

macro_rules! serialized_int {
    ($name:ident, $prim:ty, $bytes:literal) => {
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
        #[repr(transparent)]
        pub(crate) struct $name(pub(crate) [u8; $bytes]);
        unsafe impl Serialized for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.get().cmp(&other.get())
            }
        }

        impl $name {
            pub(crate) const fn get(&self) -> $prim {
                <$prim>::from_be_bytes(self.0)
            }

            pub(crate) fn set(&mut self, val: $prim) {
                self.0 = val.to_be_bytes();
            }
        }

        impl From<$prim> for $name {
            fn from(v: $prim) -> Self {
                Self(v.to_be_bytes())
            }
        }

        impl AddAssign<$prim> for $name {
            fn add_assign(&mut self, rhs: $prim) {
                self.set(self.get() + rhs);
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}_s", self.get())
            }
        }
    };
}

serialized_int!(SerializedU64, u64, 8);
serialized_int!(SerializedU32, u32, 4);
serialized_int!(SerializedU16, u16, 2);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct SerializedU48(pub(crate) [u8; 6]);
unsafe impl Serialized for SerializedU48 {}

const U48MAX: u64 = 0xffff_ffff_ffff;

impl PartialOrd for SerializedU48 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SerializedU48 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl SerializedU48 {
    pub(crate) fn get(&self) -> u64 {
        let mut buf = [0u8; 8];
        buf[2..].copy_from_slice(&self.0);
        u64::from_be_bytes(buf)
    }

    pub(crate) fn set(&mut self, val: u64) {
        mooo_assert!(val <= U48MAX);
        self.0.copy_from_slice(&val.to_be_bytes()[2..]);
    }
}

impl From<u64> for SerializedU48 {
    fn from(v: u64) -> Self {
        mooo_assert!(v <= U48MAX);
        Self(v.to_be_bytes()[2..].try_into().unwrap())
    }
}

impl AddAssign<u64> for SerializedU48 {
    fn add_assign(&mut self, rhs: u64) {
        self.set(self.get() + rhs);
    }
}

impl Display for SerializedU48 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_s", self.get())
    }
}
