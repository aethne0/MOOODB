pub(crate) fn fmt_hex(bytes: &[u8]) -> String {
    bytes
        .as_chunks()
        .0
        .iter()
        .map(|[a, b, c, d]| format!("{:02x}{:02x}{:02x}{:02x} ", a, b, c, d))
        .collect::<String>()
}
