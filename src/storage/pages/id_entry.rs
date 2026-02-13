use zerocopy::big_endian;

// --- IdEntry ---

#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    zerocopy::FromBytes,
    zerocopy::IntoBytes,
    zerocopy::Immutable,
    zerocopy::KnownLayout,
)]
pub(crate) struct U64Entry(big_endian::U64);
impl U64Entry {
    pub(crate) const SIZE_U16: u16 = size_of::<Self>() as u16;

    pub(crate) fn as_bytes(&self) -> &[u8] {
        zerocopy::IntoBytes::as_bytes(self)
    }
}

impl From<u64> for U64Entry {
    fn from(v: u64) -> Self {
        Self(v.into())
    }
}

impl From<&[u8]> for U64Entry {
    fn from(value: &[u8]) -> Self {
        zerocopy::FromBytes::read_from_bytes(&value[..size_of::<Self>()]).unwrap()
    }
}


// --- Free-page Entry ---

#[derive(Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable, zerocopy::KnownLayout)]
#[repr(C)]
pub(crate) struct FreeEntry {
    tx_id: big_endian::U64,
    page_id: big_endian::U64,
}
