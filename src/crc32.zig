//! CRC-32 (IEEE), the checksum of the log records and of the meta page.
//! It gives the same values as std.hash.Crc32, which reads one byte at a time (about 0.4 GB/s).
//! On x86-64 this uses carry-less multiply (about 25 GB/s), on ARM the CRC32X instruction,
//! and on other CPUs tables for 8 bytes at a time (about 1.6 GB/s).
const std = @import("std");
const builtin = @import("builtin");

/// CRC-32 (IEEE, the same as std.hash.Crc32) with tables for 8 bytes at a time.
const Slice8 = struct {
    const tables = blk: {
        @setEvalBranchQuota(100000);
        var t: [8][256]u32 = undefined;
        for (0..256) |i| {
            var c: u32 = i;
            for (0..8) |_| c = if (c & 1 != 0) (c >> 1) ^ 0xEDB88320 else c >> 1;
            t[0][i] = c;
        }
        for (0..256) |i| {
            for (1..8) |k| t[k][i] = (t[k - 1][i] >> 8) ^ t[0][t[k - 1][i] & 0xff];
        }
        break :blk t;
    };

    pub fn update(crc_in: u32, bytes: []const u8) u32 {
        var crc = crc_in;
        var b = bytes;
        while (b.len >= 8) {
            const lo = std.mem.readInt(u32, b[0..4], .little) ^ crc;
            const hi = std.mem.readInt(u32, b[4..8], .little);
            crc = tables[7][lo & 0xff] ^ tables[6][(lo >> 8) & 0xff] ^ tables[5][(lo >> 16) & 0xff] ^ tables[4][lo >> 24] ^
                tables[3][hi & 0xff] ^ tables[2][(hi >> 8) & 0xff] ^ tables[1][(hi >> 16) & 0xff] ^ tables[0][hi >> 24];
            b = b[8..];
        }
        for (b) |x| crc = tables[0][(crc ^ x) & 0xff] ^ (crc >> 8);
        return crc;
    }
};

const V = @Vector(2, u64);

/// Bit 0 of `imm` picks the half of `a`, bit 4 the half of `b`, as in _mm_clmulepi64_si128.
inline fn clmul(comptime imm: u8, a: V, b: V) V {
    return asm ("vpclmulqdq %[imm], %[b], %[a], %[out]"
        : [out] "=x" (-> V),
        : [a] "x" (a),
          [b] "x" (b),
          [imm] "n" (imm),
    );
}

inline fn load(p: []const u8) V {
    const v: @Vector(16, u8) = p[0..16].*;
    return @bitCast(v);
}

/// CRC-32 (IEEE) with carry-less multiply: it folds 64 bytes at a time in four 128-bit lanes
/// (Intel, "Fast CRC Computation for Generic Polynomials Using PCLMULQDQ"). The same result as std.hash.Crc32.
const Clmul = struct {
    const k1k2: V = .{ 0x0154442bd4, 0x01c6e41596 };
    const k3k4: V = .{ 0x01751997d0, 0x00ccaa009e };
    const k5k0: V = .{ 0x0163cd6124, 0 };
    const poly: V = .{ 0x01db710641, 0x01f7011641 };

    pub const available = builtin.cpu.arch == .x86_64 and builtin.cpu.has(.x86, .pclmul) and builtin.cpu.has(.x86, .avx);

    /// `crc` is the inverted running value, as in Slice8.update.
    pub fn update(crc: u32, bytes: []const u8) u32 {
        if (!available or bytes.len < 64) return Slice8.update(crc, bytes);
        var b = bytes;
        var x1 = load(b[0..]) ^ V{ crc, 0 };
        var x2 = load(b[16..]);
        var x3 = load(b[32..]);
        var x4 = load(b[48..]);
        b = b[64..];
        while (b.len >= 64) {
            x1 = clmul(0x00, x1, k1k2) ^ clmul(0x11, x1, k1k2) ^ load(b[0..]);
            x2 = clmul(0x00, x2, k1k2) ^ clmul(0x11, x2, k1k2) ^ load(b[16..]);
            x3 = clmul(0x00, x3, k1k2) ^ clmul(0x11, x3, k1k2) ^ load(b[32..]);
            x4 = clmul(0x00, x4, k1k2) ^ clmul(0x11, x4, k1k2) ^ load(b[48..]);
            b = b[64..];
        }
        x1 = clmul(0x00, x1, k3k4) ^ clmul(0x11, x1, k3k4) ^ x2;
        x1 = clmul(0x00, x1, k3k4) ^ clmul(0x11, x1, k3k4) ^ x3;
        x1 = clmul(0x00, x1, k3k4) ^ clmul(0x11, x1, k3k4) ^ x4;
        while (b.len >= 16) {
            x1 = clmul(0x00, x1, k3k4) ^ clmul(0x11, x1, k3k4) ^ load(b);
            b = b[16..];
        }
        // 128 bits to 64 bits.
        const m32: V = .{ 0xffffffff, 0 };
        var x = clmul(0x10, x1, k3k4) ^ V{ x1[1], 0 };
        const hi = V{ (x[0] >> 32) | (x[1] << 32), x[1] >> 32 };
        x = clmul(0x00, x & m32, k5k0) ^ hi;
        // Barrett reduction to 32 bits.
        var t = clmul(0x10, x & m32, poly) & m32;
        t = clmul(0x00, t, poly);
        x ^= t;
        const r: u32 = @truncate(x[0] >> 32);
        return Slice8.update(r, b);
    }
};

/// CRC-32 (IEEE) with the CRC32X instruction of ARMv8 (the "crc" feature, which Apple M chips have).
const Arm = struct {
    pub const available = builtin.cpu.arch == .aarch64 and builtin.cpu.has(.aarch64, .crc);

    pub fn update(crc_in: u32, bytes: []const u8) u32 {
        if (!available) return Slice8.update(crc_in, bytes);
        var crc = crc_in;
        var b = bytes;
        while (b.len >= 8) {
            crc = asm ("crc32x %[out:w], %[crc:w], %[v:x]"
                : [out] "=r" (-> u32),
                : [crc] "r" (crc),
                  [v] "r" (std.mem.readInt(u64, b[0..8], .little)),
            );
            b = b[8..];
        }
        for (b) |x| crc = asm ("crc32b %[out:w], %[crc:w], %[v:w]"
            : [out] "=r" (-> u32),
            : [crc] "r" (crc),
              [v] "r" (@as(u32, x)),
        );
        return crc;
    }
};

/// The fastest version that the target CPU has.
pub fn hash(bytes: []const u8) u32 {
    const update = if (Clmul.available) Clmul.update else if (Arm.available) Arm.update else Slice8.update;
    return ~update(0xffffffff, bytes);
}

test hash {
    var buf: [9000]u8 = undefined;
    var prng: std.Random.DefaultPrng = .init(7);
    prng.random().bytes(&buf);
    for (0..700) |len| for (0..8) |off| {
        const b = buf[off..][0..len];
        try std.testing.expectEqual(std.hash.Crc32.hash(b), hash(b));
        try std.testing.expectEqual(std.hash.Crc32.hash(b), ~Slice8.update(0xffffffff, b));
    };
    for ([_]usize{ 4096, 4108, 8192, 8204 }) |len|
        try std.testing.expectEqual(std.hash.Crc32.hash(buf[1..][0..len]), hash(buf[1..][0..len]));
}
