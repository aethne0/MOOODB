use crate::page::ByteOrder;

macro_rules! impl_endian {
    ($($t:ty),*) => {
        $(
            impl ByteOrder for $t {
                #[inline(always)]
                fn from_be(self) -> Self { <$t>::from_be(self) }
                #[inline(always)]
                fn to_be(self) -> Self { self.to_be() }
            }
        )*
    };
}

impl_endian!(u16, u32, u64, i16, i32, i64, usize, isize);

#[macro_export]
macro_rules! define_page_fields {
    ($($field:ident, $type:ty, $offset:expr);* $(;)?) => {
        $(
            #[inline(always)]
            pub(crate) fn $field(&self) -> $type {
                self.read_value::<$type>($offset)
            }

            paste::paste! {
            #[inline(always)]
            pub(crate) fn [<set_ $field>](&mut self, value: $type) {
                self.write_value::<$type>($offset, value);
            }
            }
        )*
    };
}
