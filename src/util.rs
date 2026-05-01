pub(crate) fn fmt_bytes(bytes: &[u8]) -> String {
    let inner: Vec<String> = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("[{}]", inner.join(" "))
}

pub(crate) fn fmt_size(size: usize) -> String {
    if size == 0 {
        return "0B".to_string();
    }

    let prefixes = ["PiB", "TiB", "GiB", "MiB", "KiB", "Bytes"];
    let mut base = 1;
    let counts: Vec<usize> = (0..prefixes.len())
        .map(|_| {
            let mut size = size;
            size %= base * 1024;
            size /= base;
            base *= 1024;
            size
        })
        .collect();

    let pairs = counts
        .iter()
        .rev()
        .enumerate()
        //.skip_while(|p| *p.1 == 0)
        .filter(|p| *p.1 > 0)
        .map(|(i, v)| format!("{}{}", v, prefixes[i]));

    /*
    format!(
        "{} ({} Bytes)",
        pairs.into_iter().collect::<Vec<_>>().join("."),
        size
    )
    */
    format!("{}", pairs.into_iter().collect::<Vec<_>>().join(" + "),)
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

#[macro_export]
macro_rules! KB {
    ($x:expr) => {
        $x * 1000
    };
}

#[macro_export]
macro_rules! MB {
    ($x:expr) => {
        $x * 1000 * 1000
    };
}

#[macro_export]
macro_rules! GB {
    ($x:expr) => {
        $x * 1000 * 1000 * 1000
    };
}

#[macro_export]
macro_rules! TB {
    ($x:expr) => {
        $x * 1000 * 1000 * 1000 * 1000
    };
}
