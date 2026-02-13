use zerocopy::big_endian;

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable, zerocopy::KnownLayout)]
#[repr(C)]
pub(super) struct CatalogEntry {
    pub(super) root_page_id: big_endian::U64,
    pub(super) object_id: big_endian::U32,
    pub(super) parent_id: big_endian::U32,
    pub(super) kind: u8,

    // for KIND_COLUMN
    pub(super) col_index: big_endian::U16,
    pub(super) col_dtype: u8,
    pub(super) col_flags: u8,

    _pad: [u8; 43],

    /// null-terminated string, max 47 bytes long (+ null byte, 48 total)
    /// NOTE must be valid ascii!
    pub(super) name: [u8; 64],
}
const _: () = assert!(size_of::<CatalogEntry>() == 128);

impl std::fmt::Display for CatalogEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match self.kind {
            Self::KIND_DB => "db",
            Self::KIND_TABLE => "table",
            Self::KIND_INDEX => "index",
            other => return write!(f, "<unknown kind {other}>"),
        };
        let name = std::str::from_utf8(&self.name)
            .unwrap_or("<invalid utf8>")
            .trim_end_matches('\0');
        write!(
            f,
            "{kind} {name:?} (db={}, id={}, root={})",
            self.parent_id.get(),
            self.object_id.get(),
            self.root_page_id.get()
        )
    }
}

impl CatalogEntry {
    pub(super) const KIND_DB: u8 = 1;
    pub(super) const KIND_TABLE: u8 = 2;
    pub(super) const KIND_INDEX: u8 = 3;
    pub(super) const KIND_COLUMN: u8 = 4;

    fn internal_new(
        kind: u8, object_id: u32, parent_id: u32, root_page_id: u64, col_index: u16, col_dtype: u8, col_flags: u8,
        name: &[u8; 64],
    ) -> Self {
        assert!(name.is_ascii(), "catalog entry name must be valid ascii");
        Self {
            kind,
            root_page_id: root_page_id.into(),
            parent_id: parent_id.into(),
            object_id: object_id.into(),
            col_index: col_index.into(),
            col_dtype,
            col_flags,
            name: *name,
            _pad: [0; _],
        }
    }

    pub(super) fn new_db(parent_id: u32, object_id: u32, root_page_id: u64, name: &[u8; 64]) -> Self {
        Self::internal_new(Self::KIND_DB, object_id, parent_id, root_page_id, 0, 0, 0, name)
    }

    pub(super) fn new_table(parent_id: u32, object_id: u32, root_page_id: u64, name: &[u8; 64]) -> Self {
        Self::internal_new(Self::KIND_TABLE, object_id, parent_id, root_page_id, 0, 0, 0, name)
    }

    pub(super) fn new_index(parent_id: u32, object_id: u32, root_page_id: u64, name: &[u8; 64]) -> Self {
        Self::internal_new(Self::KIND_INDEX, object_id, parent_id, root_page_id, 0, 0, 0, name)
    }

    pub(super) fn new_column(
        parent_id: u32, object_id: u32, root_page_id: u64, name: &[u8; 64], col_index: u16, col_dtype: u8,
        col_flags: u8,
    ) -> Self {
        Self::internal_new(Self::KIND_COLUMN, object_id, parent_id, root_page_id, col_index, col_dtype, col_flags, name)
    }

    pub(super) fn to_bytes(&self) -> &[u8] {
        zerocopy::IntoBytes::as_bytes(self)
    }

    pub(super) fn from_bytes(buf: &[u8]) -> Self {
        let cat: Self =
            zerocopy::FromBytes::read_from_bytes(buf).expect("catalog entry buffer must be correctly sized");
        assert!(cat.name.is_ascii(), "catalog entry name must be valid ascii");
        cat
    }
}
