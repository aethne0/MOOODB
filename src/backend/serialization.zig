const std = @import("std");
const mem = std.mem;

pub const PAGE_HEADER_SIZE: u16 = 0x40;
pub const END_OF_PAGE: u16 = 0x1000 - 1;

pub const SerializedU16 = extern struct {
    bytes: [2]u8,

    pub fn get(self: SerializedU16) u16 {
        return mem.readInt(u16, &self.bytes, .big);
    }

    pub fn set(self: *SerializedU16, val: u16) void {
        mem.writeInt(u16, &self.bytes, val, .big);
    }
};

pub const SerializedU64 = extern struct {
    bytes: [8]u8,

    pub fn get(self: SerializedU64) u64 {
        return mem.readInt(u64, &self.bytes, .big);
    }

    pub fn set(self: *SerializedU64, val: u64) void {
        mem.writeInt(u64, &self.bytes, val, .big);
    }
};

/// The first 32 bytes of every page on disk, regardless of page type.
/// Layout (big-endian): checksum u64 | pgid u64 | txid u64 | pgtype u64
pub const PagePrefix = extern struct {
    checksum: SerializedU64,
    pgid:     SerializedU64,
    txid:     SerializedU64,
    pgtype:   SerializedU64,
};

/// Packed page+slot pointer: upper 48 bits = pgid, lower 16 bits = slot index.
pub const HeapPtr = extern struct {
    inner: SerializedU64,

    pub fn new(pgid_val: u64, slot_index: u16) HeapPtr {
        return .{ .inner = SerializedU64{ .bytes = @bitCast(std.mem.nativeToBig(u64, (pgid_val << 16) | slot_index)) } };
    }

    pub fn pgid(self: HeapPtr) u64 {
        return (self.inner.get() >> 16);
    }

    pub fn slot(self: HeapPtr) u16 {
        return @intCast(self.inner.get() & 0xffff);
    }
};

comptime {
    std.debug.assert(@sizeOf(SerializedU16) == 2);
    std.debug.assert(@sizeOf(SerializedU64) == 8);
    std.debug.assert(@sizeOf(PagePrefix) == 32);
    std.debug.assert(@sizeOf(HeapPtr) == 8);
}
