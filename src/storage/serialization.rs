use std::ops::AddAssign;

use crate::mooo_assert;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub(super) struct SerializedU64([u8; 8]);
unsafe impl ByteToFrom for SerializedU64 {}

impl PartialOrd for SerializedU64 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SerializedU64 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl SerializedU64 {
    pub(super) const fn get(&self) -> u64 {
        u64::from_be_bytes(self.0)
    }

    pub(super) fn set(&mut self, val: u64) {
        self.0 = val.to_be_bytes();
    }
}

impl From<u64> for SerializedU64 {
    fn from(v: u64) -> Self {
        Self(v.to_be_bytes())
    }
}

impl AddAssign<u64> for SerializedU64 {
    fn add_assign(&mut self, rhs: u64) {
        self.set(self.get() + rhs);
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
pub(super) struct SerializedU16([u8; 2]);
unsafe impl ByteToFrom for SerializedU16 {}

impl PartialOrd for SerializedU16 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SerializedU16 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl SerializedU16 {
    pub(super) const fn get(&self) -> u16 {
        u16::from_be_bytes(self.0)
    }

    pub(super) fn set(&mut self, val: u16) {
        self.0 = val.to_be_bytes();
    }
}

impl From<u16> for SerializedU16 {
    fn from(v: u16) -> Self {
        Self(v.to_be_bytes())
    }
}

/// # SAFETY
/// POD `#[repr(C)]` or `#[repr(transparent)]` only!!
pub(super) unsafe trait ByteToFrom: Sized {
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
