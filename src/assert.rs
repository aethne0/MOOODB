#[macro_export]
macro_rules! mooo_assert {
    ($($arg:tt)*) => { assert!($($arg)*) };
}
