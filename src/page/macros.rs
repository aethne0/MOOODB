#[macro_export]
macro_rules! define_page_fields {
    ($($field:ident, $type:ty, $offset:expr);* $(;)?) => {
        paste::paste! {
            $(
                #[inline(always)]
                pub(crate) fn $field(&self) -> $type {
                    // Assuming read_ methods follow a pattern like read_u16
                    self.[<read_ $type>]($offset)
                }

                #[inline(always)]
                pub(crate) fn [<set_ $field>](&mut self, value: $type) {
                    self.[<write_$type>]($offset, value);
                }
            )*
        }
    };
}

#[macro_export]
macro_rules! generate_primitive_accessors {
    ($($t:ty),*) => {
        paste::paste! {
            $(
                #[inline(always)]
                pub(crate) fn [<read_ $t>](&self, offset: usize) -> $t {
                    $t::from_be_bytes(
                        self.raw[offset..offset + std::mem::size_of::<$t>()]
                            .try_into()
                            .unwrap(),
                    )
                }

                #[inline(always)]
                pub(crate) fn [<write_ $t>](&mut self, offset: usize, value: $t) {
                    self.raw[offset..offset + std::mem::size_of::<$t>()]
                        .copy_from_slice(&value.to_be_bytes());
                }
            )*
        }
    };
}
