#[cfg(test)]
mod test;

mod btree;
mod frame;
pub(crate) mod manager;
mod pages;
mod slab;

pub(crate) mod pager;
pub(crate) const PAGE_SIZE_U16: u16 = 4096;
pub(crate) const PAGE_SIZE: usize = PAGE_SIZE_U16 as usize;
pub(crate) const PAGE_ID_NULL: u64 = u64::MAX;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) enum StorageError {
    Io(std::io::ErrorKind),
    Checksum,
    Poisoned,
}

impl From<std::io::ErrorKind> for StorageError {
    fn from(value: std::io::ErrorKind) -> Self {
        StorageError::Io(value)
    }
}

impl std::fmt::Display for StorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StorageError::Io(kind) => write!(f, "I/O error: {kind}"),
            StorageError::Checksum => write!(f, "checksum mismatch"),
            StorageError::Poisoned => write!(f, "storage poisoned"),
        }
    }
}
