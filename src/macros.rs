/// Generates getter-only field accessors that call `read_TYPE(offset)`.
/// Use in an `impl<B: AsRef<[u8]>>` block alongside `accessors_read!`.
#[macro_export]
macro_rules! page_fields_ro {
    ($($field:ident, $type:ty, $offset:expr);* $(;)?) => {
        paste::paste! {
            $(
                pub(crate) fn $field(&self) -> $type {
                    self.[<read_ $type>]($offset)
                }
            )*
        }
    };
}

/// Generates setter-only field accessors that call `write_TYPE(offset, value)`.
/// Use in an `impl<B: AsRef<[u8]> + AsMut<[u8]>>` block alongside `accessors_write!`.
#[macro_export]
macro_rules! page_fields_set {
    ($($field:ident, $type:ty, $offset:expr);* $(;)?) => {
        paste::paste! {
            $(
                pub(crate) fn [<set_ $field>](&mut self, value: $type) {
                    self.[<write_ $type>]($offset, value);
                }
            )*
        }
    };
}

/// Generates both getter and setter field accessors. Convenience wrapper for
/// concrete (non-generic) types that use `accessors!` for a `&mut` raw buffer.
#[macro_export]
macro_rules! page_fields {
    ($($field:ident, $type:ty, $offset:expr);* $(;)?) => {
        $crate::page_fields_ro!($($field, $type, $offset);*);
        $crate::page_fields_set!($($field, $type, $offset);*);
    };
}

/// Generates `read_T` methods using `self.raw.as_ref()`.
/// Use in an `impl<B: AsRef<[u8]>>` block.
#[macro_export]
macro_rules! accessors_read {
    ($($t:ty),*) => {
        paste::paste! {
            $(
                pub(crate) fn [<read_ $t>](&self, offset: u16) -> $t {
                    let offset = offset as usize;
                    $t::from_be_bytes(
                        self.raw.as_ref()[offset..offset + std::mem::size_of::<$t>()]
                            .try_into()
                            .unwrap(),
                    )
                }
            )*
        }
    };
}

/// Generates `write_T` methods using `self.raw.as_mut()`.
/// Use in an `impl<B: AsMut<[u8]>>` block.
#[macro_export]
macro_rules! accessors_write {
    ($($t:ty),*) => {
        paste::paste! {
            $(
                pub(crate) fn [<write_ $t>](&mut self, offset: u16, value: $t) {
                    let offset = offset as usize;
                    self.raw.as_mut()[offset..offset + std::mem::size_of::<$t>()]
                        .copy_from_slice(&value.to_be_bytes());
                }
            )*
        }
    };
}

/// Generates both `read_T` and `write_T` using direct `self.raw` indexing.
/// For concrete types where `raw` is `&mut [u8; N]` (e.g. `PageSuperblock`).
#[macro_export]
macro_rules! accessors {
    ($($t:ty),*) => {
        paste::paste! {
            $(
                pub(crate) fn [<read_ $t>](&self, offset: u16) -> $t {
                    let offset = offset as usize;
                    $t::from_be_bytes(
                        self.raw[offset..offset + std::mem::size_of::<$t>()]
                            .try_into()
                            .unwrap(),
                    )
                }

                pub(crate) fn [<write_ $t>](&mut self, offset: u16, value: $t) {
                    let offset = offset as usize;
                    self.raw[offset..offset + std::mem::size_of::<$t>()]
                        .copy_from_slice(&value.to_be_bytes());
                }
            )*
        }
    };
}

#[macro_export]
macro_rules! Bytes {
    ($x:expr) => {
        $x
    };
}

#[macro_export]
macro_rules! KiB {
    ($x:expr) => {
        $x * 1024
    };
}

#[macro_export]
macro_rules! MiB {
    ($x:expr) => {
        $x * 1024 * 1024
    };
}

#[macro_export]
macro_rules! GiB {
    ($x:expr) => {
        $x * 1024 * 1024 * 1024
    };
}

#[macro_export]
macro_rules! TiB {
    ($x:expr) => {
        $x * 1024 * 1024 * 1024 * 1024
    };
}
