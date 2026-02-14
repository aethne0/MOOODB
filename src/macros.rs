#[macro_export]
macro_rules! page_fields {
    ($($field:ident, $type:ty, $offset:expr);* $(;)?) => {
        paste::paste! {
            $(
                pub(crate) fn $field(&self) -> $type {
                    // Assuming read_ methods follow a pattern like read_u16
                    self.[<read_ $type>]($offset)
                }

                pub(crate) fn [<set_ $field>](&mut self, value: $type) {
                    self.[<write_$type>]($offset, value);
                }
            )*
        }
    };
}

#[macro_export]
macro_rules! accessors {
    ($($t:ty),*) => {
        paste::paste! {
            $(
                /// Handles endianness
                pub(crate) fn [<read_ $t>](&self, offset: u16) -> $t {
                    let offset = offset as usize;
                    $t::from_be_bytes(
                        self.raw[offset..offset + std::mem::size_of::<$t>()]
                            .try_into()
                            .unwrap(),
                    )
                }

                /// Handles endianness
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
