const std = @import("std");
const build_options = @import("build_options");
const Io = std.Io;
const Allocator = std.mem.Allocator;

pub const PAGE_SIZE = build_options.page_size;
pub const POOL_FRAMES = build_options.pool_frames;

pub const MAX_KEY = PAGE_SIZE / 16;
pub const MAX_VAL = PAGE_SIZE / 8;
pub const MAX_DEPTH = 32;

const HDR = 12;
const CAPACITY = PAGE_SIZE - HDR;
const MIN_FILL = CAPACITY / 4;

comptime {
    std.debug.assert(PAGE_SIZE >= 256 and PAGE_SIZE <= 32768);
}

pub const META_PGNO = 0;
pub const MAGIC = "BPTDISK1";

pub const Error = error{ BadFile, KeyTooLarge };

fn get16(p: []const u8) u16 {
    return std.mem.readInt(u16, p[0..2], .little);
}

fn get32(p: []const u8) u32 {
    return std.mem.readInt(u32, p[0..4], .little);
}

fn put16(p: []u8, v: u16) void {
    return std.mem.writeInt(u16, p[0..2], v, .little);
}

fn put32(p: []u8, v: u32) void {
    return std.mem.writeInt(u32, p[0..4], v, .little);
}

const Frame = struct {
    pgno: u32,
    pins: i32,
    dirty: bool,
    used: bool,
    last_used: u64,
};

const PathEntry = struct {
    pgno: u32,
    idx: usize,
};

pub const BPTree = struct {
    io: Io,
    file: Io.File,
    root: u32 = 0,
    npages: u32 = 0,
    freelist: u32 = 0,
    frames: [POOL_FRAMES]Frame = @splat(.{ .pgno = 0, .pins = 0, .dirty = false, .used = false, .last_used = 0 }),
    mem: []u8,
    tick: u64 = 0,
    reads: u64 = 0,
    writes: u64 = 0,

    pub fn init(gpa: Allocator, io: Io, path: []const u8) !*BPTree {
        const t = try gpa.create(BPTree);
        errdefer gpa.destroy(t);
        const file = try Io.Dir.cwd().createFile(io, path, .{ .read = true, .truncate = false });
        errdefer file.close(io);
        const mem = try gpa.alloc(u8, PAGE_SIZE * POOL_FRAMES);
        errdefer gpa.free(mem);
        t.* = .{ .io = io, .file = file, .mem = mem };

        const size = try file.length(io);

        if (size == 0) {
            t.npages = 1;
            const root = try t.pageAlloc(.leaf);
            t.root = t.pgnoOf(root);
            t.poolUnpin(root, true);
        } else if (!try t.metaRead()) {
            return Error.BadFile;
        }

        return t;
    }

    pub fn deinit(self: *BPTree, gpa: Allocator) void {
        std.debug.assert(self.poolPinned() == 0);
        self.poolFlush() catch {};
        self.metaWrite() catch {};
        self.file.sync(self.io) catch |err| std.debug.panic("fsync: {t}", .{err});
        self.file.close(self.io);
        gpa.free(self.mem);
        gpa.destroy(self);
    }

    fn diskRead(self: *BPTree, pgno: u32, buf: []u8) !void {
        const n = try self.file.readPositionalAll(self.io, buf[0..PAGE_SIZE], @as(u64, pgno) * PAGE_SIZE);
        if (n < PAGE_SIZE) @memset(buf[n..PAGE_SIZE], 0);
        self.reads += 1;
    }

    fn diskWrite(self: *BPTree, pgno: u32, buf: []const u8) !void {
        try self.file.writePositionalAll(self.io, buf[0..PAGE_SIZE], @as(u64, pgno) * PAGE_SIZE);
        self.writes += 1;
    }

    fn metaWrite(self: *BPTree) !void {
        var buf: [PAGE_SIZE]u8 = @splat(0);
        @memcpy(buf[0..MAGIC.len], MAGIC);
        put32(buf[8..], @intCast(PAGE_SIZE));
        put32(buf[12..], self.root);
        put32(buf[16..], self.npages);
        put32(buf[20..], self.freelist);
        try self.diskWrite(META_PGNO, &buf);
    }

    fn metaRead(self: *BPTree) !bool {
        var buf: [PAGE_SIZE]u8 = undefined;
        try self.diskRead(META_PGNO, &buf);

        if (!std.mem.eql(u8, MAGIC, buf[0..MAGIC.len]) or get32(buf[8..]) != PAGE_SIZE) return false;
        self.root = get32(buf[12..]);
        self.npages = get32(buf[16..]);
        self.freelist = get32(buf[20..]);
        return true;
    }

    fn frameData(self: *BPTree, f: usize) []u8 {
        return self.mem[PAGE_SIZE * f ..][0..PAGE_SIZE];
    }

    fn frameOf(self: *BPTree, page: []const u8) usize {
        return (@intFromPtr(page.ptr) - @intFromPtr(self.mem.ptr)) / PAGE_SIZE;
    }

    fn poolVictim(self: *BPTree) !usize {
        var victim: ?usize = null;
        for (0..POOL_FRAMES) |f| {
            const fr = &self.frames[f];
            if (!fr.used) return f;
            if (fr.pins == 0 and (victim == null or fr.last_used < self.frames[victim.?].last_used))
                victim = f;
        }
        const best = victim orelse unreachable;
        const fr = &self.frames[best];
        if (fr.dirty) try self.diskWrite(fr.pgno, self.frameData(best));
        fr.used = false;
        fr.dirty = false;
        return best;
    }

    fn poolPin(self: *BPTree, pgno: u32, load: bool) ![]u8 {
        std.debug.assert(pgno != META_PGNO and pgno < self.npages);
        for (0..POOL_FRAMES) |f| {
            const fr = &self.frames[f];
            if (fr.used and fr.pgno == pgno) {
                fr.pins += 1;
                self.tick += 1;
                fr.last_used = self.tick;
                return self.frameData(f);
            }
        }
        const f = try self.poolVictim();
        if (load) try self.diskRead(pgno, self.frameData(f));
        self.tick += 1;
        self.frames[f] = .{ .pgno = pgno, .pins = 1, .dirty = false, .used = true, .last_used = self.tick };
        return self.frameData(f);
    }

    fn poolGet(self: *BPTree, pgno: u32) !Page {
        return .{ .page = (try self.poolPin(pgno, true))[0..PAGE_SIZE] };
    }

    fn poolUnpin(self: *BPTree, page: Page, dirty: bool) void {
        const fr = &self.frames[self.frameOf(page.page)];
        std.debug.assert(fr.used and fr.pins > 0);
        fr.pins -= 1;
        if (dirty) fr.dirty = true;

        if (build_options.pool_paranoid) {
            if (fr.pins == 0) {
                if (fr.dirty) self.diskWrite(fr.pgno, page.page) catch |err| std.debug.panic("poolUnpin: {t}", .{err});
                fr.used = false;
                fr.dirty = false;
                @memset(page.page, 0xAA);
            }
        }
    }

    fn pgnoOf(self: *BPTree, page: Page) u32 {
        return self.frames[self.frameOf(page.page)].pgno;
    }

    fn poolFlush(self: *BPTree) !void {
        for (0..POOL_FRAMES) |f| {
            const fr = &self.frames[f];
            if (fr.used and fr.dirty) {
                try self.diskWrite(fr.pgno, self.frameData(f));
                fr.dirty = false;
            }
        }
    }

    fn poolPinned(self: *BPTree) i32 {
        var n: i32 = 0;
        for (0..POOL_FRAMES) |f| {
            n += self.frames[f].pins;
        }
        return n;
    }

    fn pageAlloc(self: *BPTree, t: Page.Type) !Page {
        var pgno: u32 = undefined;
        if (self.freelist != 0) {
            pgno = self.freelist;
            const p = try self.poolGet(pgno);
            std.debug.assert(p.getType() == .free);
            self.freelist = p.getLink();
            p.init(t);
            return p;
        }
        pgno = self.npages;
        self.npages += 1;
        const p: Page = .{ .page = (try self.poolPin(pgno, false))[0..PAGE_SIZE] };
        p.init(t);
        return p;
    }

    fn pageFree(self: *BPTree, p: Page) void {
        const pgno = self.pgnoOf(p);
        p.init(.free);
        p.setLink(self.freelist);
        self.freelist = pgno;
        self.poolUnpin(p, true);
    }

    fn descend(self: *BPTree, key: []const u8, path: []PathEntry, depth: *usize) !Page {
        var pgno = self.root;
        var d: usize = 0;
        while (true) {
            const p = try self.poolGet(pgno);
            path[d].pgno = pgno;
            if (p.getType() == .leaf) {
                depth.* = d;
                return p;
            }
            const i = p.childIndex(key);
            path[d].idx = i;
            pgno = p.getChild(i);
            self.poolUnpin(p, false);
            d += 1;
            std.debug.assert(d < MAX_DEPTH);
        }
    }

    pub fn get(self: *BPTree, key: []const u8, out: []u8) !?[]u8 {
        if (key.len > MAX_KEY) return error.KeyTooLarge;
        var path: [MAX_DEPTH]PathEntry = undefined;
        var depth: usize = undefined;
        const leaf = try self.descend(key, &path, &depth);
        defer self.poolUnpin(leaf, false);
        const r = leaf.search(key);
        if (r.found) {
            const val = leaf.getLeafVal(r.index);
            if (out.len < val.len) return error.NoSpaceLeft;
            @memcpy(out[0..val.len], val);
            return out[0..val.len];
        }
        return null;
    }

    /// returns true if split happened
    fn insertUp(self: *BPTree, path: []const PathEntry, d: usize, idx: usize, c: []const u8) !bool {
        const pgno = path[d].pgno;
        const p = try self.poolGet(pgno);
        if (p.insertCell(idx, c)) {
            self.poolUnpin(p, true);
            return false;
        }

        const S = struct {
            var cl: CellList = undefined;
        };
        const cl = &S.cl;
        cl.reset();
        for (0..p.getN()) |i| {
            if (i == idx) cl.add(c);
            cl.add(p.getCell(i));
        }
        if (idx == p.getN()) cl.add(c);

        const leaf = p.getType() == .leaf;
        const s = cl.chooseSplit(leaf);
        const right = self.pageAlloc(p.getType()) catch |e| {
            self.poolUnpin(p, false);
            return e;
        };
        const right_pg = self.pgnoOf(right);
        var sep: [MAX_KEY + 6]u8 = undefined;
        var sep_sz: usize = undefined;

        if (leaf) {
            right.fill(.leaf, p.getLink(), cl, s, cl.n);
            p.fill(.leaf, right_pg, cl, 0, s);
            const k = right.getCellKey(0);
            sep_sz = makeInternalCell(&sep, right_pg, k);
        } else {
            const mid = cl.cell[s];
            right.fill(.internal, get32(mid), cl, s + 1, cl.n);
            p.fill(.internal, p.getLink(), cl, 0, s);
            sep_sz = makeInternalCell(&sep, right_pg, mid[6..][0..get16(mid[4..])]);
        }
        self.poolUnpin(right, true);
        self.poolUnpin(p, true);

        if (d == 0) {
            const root = try self.pageAlloc(.internal);
            root.setLink(pgno);
            _ = root.insertCell(0, sep[0..sep_sz]);
            self.root = self.pgnoOf(root);
            self.poolUnpin(root, true);
        } else {
            const ok = try self.insertUp(path, d - 1, path[d - 1].idx, sep[0..sep_sz]);
            std.debug.assert(ok);
        }
        return true;
    }
};

pub const Page = struct {
    page: *[PAGE_SIZE]u8,

    pub const Type = enum(u8) {
        free = 0,
        leaf = 1,
        internal = 2,
    };

    fn init(self: Page, t: Type) void {
        @memset(self.page[0..PAGE_SIZE], 0);
        self.page[0] = @backingInt(t);
        self.setCellStart(PAGE_SIZE);
    }

    fn getType(self: Page) Type {
        return @fromBackingInt(@intCast(self.page[0]));
    }

    fn getN(self: Page) u16 {
        return get16(self.page[2..]);
    }
    fn getCellStart(self: Page) u16 {
        return get16(self.page[4..]);
    }
    fn getFrag(self: Page) u16 {
        return get16(self.page[6..]);
    }
    fn getLink(self: Page) u32 {
        return get32(self.page[8..12]);
    }

    fn setN(self: Page, n: usize) void {
        put16(self.page[2..], @intCast(n));
    }
    fn setCellStart(self: Page, v: usize) void {
        put16(self.page[4..], @intCast(v));
    }
    fn setFrag(self: Page, v: usize) void {
        put16(self.page[6..], @intCast(v));
    }
    fn setLink(self: Page, v: u32) void {
        put32(self.page[8..], v);
    }

    fn getSlot(self: Page, i: usize) u16 {
        return get16(self.page[HDR + 2 * i ..]);
    }
    fn setSlot(self: Page, i: usize, off: usize) void {
        put16(self.page[HDR + 2 * i ..], @intCast(off));
    }
    fn getCellSize(self: Page, c: []const u8) usize {
        if (self.getType() == .leaf) return 4 + @as(usize, get16(c)) + get16(c[2..]);
        return 6 + @as(usize, get16(c[4..]));
    }
    fn getCell(self: Page, i: usize) []const u8 {
        const c = self.page[self.getSlot(i)..];
        return c[0..self.getCellSize(c)];
    }
    fn getCellKey(self: Page, i: usize) []const u8 {
        const c = self.getCell(i);
        if (self.getType() == .leaf) {
            const klen = get16(c);
            return c[4..][0..klen];
        } else {
            const klen = get16(c[4..]);
            return c[6..][0..klen];
        }
    }
    fn getLeafVal(self: Page, i: usize) []const u8 {
        const c = self.getCell(i);
        const vlen = get16(c[2..4]);
        return c[4 + get16(c) ..][0..vlen];
    }

    fn getChild(self: Page, i: usize) u32 {
        return if (i == 0) self.getLink() else get32(self.getCell(i - 1));
    }

    fn getUsedBytes(self: Page) usize {
        return CAPACITY - (self.getCellStart() - HDR - 2 * @as(usize, self.getN())) - self.getFrag();
    }

    fn getFreeBytes(self: Page) usize {
        return CAPACITY - self.getUsedBytes();
    }

    const SearchResult = struct {
        found: bool,
        index: usize,
    };
    fn search(self: Page, key: []const u8) SearchResult {
        var lo: u16 = 0;
        var hi: u16 = self.getN();
        while (lo < hi) {
            const mid = (lo + hi) / 2;
            const mkey = self.getCellKey(@intCast(mid));
            if (std.mem.lessThan(u8, mkey, key)) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        const found = if (lo < self.getN()) std.mem.eql(u8, key, self.getCellKey(@intCast(lo))) else false;
        return .{ .found = found, .index = @intCast(lo) };
    }

    fn compact(self: Page) void {
        var tmp: [PAGE_SIZE]u8 = undefined;
        const tmp_page: Page = .{ .page = &tmp };
        @memcpy(&tmp, self.page);
        var top: usize = PAGE_SIZE;
        const n = self.getN();
        for (0..n) |i| {
            const c = tmp_page.getCell(i);
            top -= c.len;
            @memcpy(self.page[top..][0..c.len], c);
            self.setSlot(i, top);
        }
        self.setCellStart(top);
        self.setFrag(0);
    }

    fn insertCell(self: Page, idx: usize, c: []const u8) bool {
        if (self.getFreeBytes() < c.len + 2) return false;
        const n: usize = self.getN();
        if (self.getCellStart() - (HDR + 2 * n) < c.len + 2)
            self.compact();
        const off: usize = self.getCellStart() - c.len;
        @memcpy(self.page[off..][0..c.len], c);
        self.setCellStart(off);

        const s = (2 * (n - idx));
        @memmove(self.page[HDR + 2 * (idx + 1) ..][0..s], self.page[HDR + 2 * idx ..][0..s]);
        self.setSlot(idx, off);
        self.setN(n + 1);
        return true;
    }

    fn deleteCell(self: Page, idx: usize) void {
        const n: usize = self.getN();
        const off = self.getSlot(idx);
        const sz = self.getCell(idx).len;
        if (off == self.getCellStart()) {
            self.setCellStart(off + sz);
        } else {
            self.setFrag(self.getFrag() + sz);
        }
        const s = 2 * (n - idx - 1);
        @memmove(self.page[HDR + 2 * idx ..][0..s], self.page[HDR + 2 * (idx + 1) ..][0..s]);
        self.setN(n - 1);
    }

    fn childIndex(self: Page, key: []const u8) usize {
        const e = self.search(key);
        return if (e.found) e.index + 1 else e.index;
    }

    fn fill(self: Page, t: Type, link: u32, cl: *const CellList, from: usize, to: usize) void {
        self.init(t);
        self.setLink(link);
        for (from..to) |i| {
            const ok = self.insertCell(i - from, cl.cell[i]);
            std.debug.assert(ok);
        }
    }
};

fn makeLeafCell(out: []u8, k: []const u8, v: []const u8) usize {
    put16(out, @intCast(k.len));
    put16(out[2..], @intCast(v.len));
    @memcpy(out[4..][0..k.len], k);
    @memcpy(out[4 + k.len ..][0..v.len], v);
    return 4 + k.len + v.len;
}

fn makeInternalCell(out: []u8, child_pg: u32, k: []const u8) usize {
    put32(out, child_pg);
    put16(out[4..], @intCast(k.len));
    @memcpy(out[6..][0..k.len], k);
    return 6 + k.len;
}

const CellList = struct {
    n: usize = 0,
    cell: [PAGE_SIZE / 2][]const u8 = undefined,
    buf: [2 * PAGE_SIZE]u8 = undefined,
    used: usize = 0,

    fn reset(self: *CellList) void {
        self.n = 0;
        self.used = 0;
    }

    fn add(self: *CellList, c: []const u8) void {
        const dst = self.buf[self.used..][0..c.len];
        @memcpy(dst, c);
        self.cell[self.n] = dst;
        self.n += 1;
        self.used += c.len;
    }

    fn addPage(self: *CellList, p: Page) void {
        for (0..p.getN()) |i| self.add(p.getCell(i));
    }

    fn bytes(self: *const CellList, from: usize, to: usize) usize {
        var b: usize = 0;
        for (from..to) |i| b += self.cell[i].len + 2;
        return b;
    }

    fn chooseSplit(self: *const CellList, leaf: bool) usize {
        std.debug.assert(self.n >= 2);
        var best: ?usize = null;
        var best_worst: usize = 0;
        const hi = if (leaf) self.n - 1 else self.n - 2;

        for (1..hi + 1) |s| {
            const l = self.bytes(0, s);
            const r = self.bytes(if (leaf) s else s + 1, self.n);
            const worst = @max(l, r);
            if (best == null or worst < best_worst) {
                best = s;
                best_worst = worst;
            }
        }

        std.debug.assert(best != null and best_worst <= CAPACITY);
        return best.?;
    }
};

test BPTree {
    const io = std.testing.io;
    const gpa = std.testing.allocator;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const name = "test.bin";
    const file = try tmp.dir.createFile(io, name, .{});
    defer file.close(io);
    const path = try tmp.dir.realPathFileAlloc(io, name, gpa);
    defer gpa.free(path);

    const t: *BPTree = try .init(gpa, io, path);
    defer t.deinit(gpa);

    try t.metaWrite();
    try std.testing.expect(try t.metaRead());
}

test Page {
    var buf: [PAGE_SIZE]u8 = undefined;
    var cell: [PAGE_SIZE]u8 = undefined;

    const leaf: Page = .{ .page = &buf };
    leaf.init(.leaf);
    try std.testing.expectEqual(.leaf, leaf.getType());
    try std.testing.expectEqual(CAPACITY, leaf.getFreeBytes());

    const keys = [_][]const u8{ "delta", "alpha", "charlie", "bravo" };
    for (keys) |k| {
        const sz = makeLeafCell(&cell, k, "value");
        const r = leaf.search(k);
        try std.testing.expect(!r.found);
        try std.testing.expect(leaf.insertCell(r.index, cell[0..sz]));
    }
    try std.testing.expectEqual(4, leaf.getN());
    try std.testing.expectEqualStrings("alpha", leaf.getCellKey(0));
    try std.testing.expectEqualStrings("delta", leaf.getCellKey(3));
    try std.testing.expectEqualStrings("value", leaf.getLeafVal(2));

    const r = leaf.search("alpha");
    try std.testing.expect(r.found);
    leaf.deleteCell(r.index);
    try std.testing.expectEqual(3, leaf.getN());
    try std.testing.expect(leaf.getFrag() > 0);

    const used = leaf.getUsedBytes();
    leaf.compact();
    try std.testing.expectEqual(0, leaf.getFrag());
    try std.testing.expectEqual(used, leaf.getUsedBytes());
    try std.testing.expectEqualStrings("bravo", leaf.getCellKey(0));
    try std.testing.expectEqualStrings("charlie", leaf.getCellKey(1));
    try std.testing.expectEqualStrings("delta", leaf.getCellKey(2));

    // Fill the page; insertCell must compact the fragmented space before it gives up.
    var i: usize = 0;
    while (true) : (i += 1) {
        var kbuf: [8]u8 = undefined;
        const k = std.fmt.bufPrint(&kbuf, "k{d:0>6}", .{i}) catch unreachable;
        const sz = makeLeafCell(&cell, k, "v");
        if (!leaf.insertCell(leaf.search(k).index, cell[0..sz])) break;
    }
    try std.testing.expect(leaf.getFreeBytes() < 4 + 7 + 1 + 2);

    const internal: Page = .{ .page = &buf };
    internal.init(.internal);
    internal.setLink(7);
    const sz = makeInternalCell(&cell, 9, "mid");
    try std.testing.expect(internal.insertCell(0, cell[0..sz]));
    try std.testing.expectEqual(7, internal.getChild(0));
    try std.testing.expectEqual(9, internal.getChild(1));
    try std.testing.expectEqualStrings("mid", internal.getCellKey(0));
}

test "BPTree pool" {
    const io = std.testing.io;
    const gpa = std.testing.allocator;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const name = "pool.bin";
    const file = try tmp.dir.createFile(io, name, .{});
    defer file.close(io);
    const path = try tmp.dir.realPathFileAlloc(io, name, gpa);
    defer gpa.free(path);

    const t: *BPTree = try .init(gpa, io, path);
    defer t.deinit(gpa);

    t.npages = POOL_FRAMES + 4;
    for (1..t.npages) |pg| {
        const p: Page = .{ .page = (try t.poolPin(@intCast(pg), false))[0..PAGE_SIZE] };
        p.init(.leaf);
        try std.testing.expectEqual(pg, t.pgnoOf(p));
        t.poolUnpin(p, true);
    }
    try std.testing.expectEqual(0, t.poolPinned());

    const p = try t.poolGet(1);
    try std.testing.expectEqual(.leaf, p.getType());
    t.poolUnpin(p, false);
    try std.testing.expectEqual(0, t.poolPinned());
    try t.poolFlush();
}

test "BPTree page alloc" {
    const io = std.testing.io;
    const gpa = std.testing.allocator;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const name = "alloc.bin";
    const file = try tmp.dir.createFile(io, name, .{});
    defer file.close(io);
    const path = try tmp.dir.realPathFileAlloc(io, name, gpa);
    defer gpa.free(path);

    const t: *BPTree = try .init(gpa, io, path);
    defer t.deinit(gpa);

    // open allocates the root leaf as page 1.
    try std.testing.expectEqual(1, t.root);
    try std.testing.expectEqual(2, t.npages);

    const a = try t.pageAlloc(.leaf);
    const a_pgno = t.pgnoOf(a);
    try std.testing.expectEqual(2, a_pgno);
    try std.testing.expectEqual(.leaf, a.getType());
    try std.testing.expectEqual(3, t.npages);

    t.pageFree(a);
    try std.testing.expectEqual(a_pgno, t.freelist);

    const b = try t.pageAlloc(.internal);
    try std.testing.expectEqual(a_pgno, t.pgnoOf(b));
    try std.testing.expectEqual(.internal, b.getType());
    try std.testing.expectEqual(0, t.freelist);
    try std.testing.expectEqual(3, t.npages);
    t.poolUnpin(b, true);
    try std.testing.expectEqual(0, t.poolPinned());
}

test "BPTree get" {
    const io = std.testing.io;
    const gpa = std.testing.allocator;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const name = "get.bin";
    const file = try tmp.dir.createFile(io, name, .{});
    defer file.close(io);
    const path = try tmp.dir.realPathFileAlloc(io, name, gpa);
    defer gpa.free(path);

    const t: *BPTree = try .init(gpa, io, path);
    defer t.deinit(gpa);

    // Make a two-level tree by hand: the root holds "m", with "a" on the left and "m", "z" on the right.
    var cell: [PAGE_SIZE]u8 = undefined;
    const left = try t.poolGet(t.root);
    var sz = makeLeafCell(&cell, "a", "1");
    try std.testing.expect(left.insertCell(0, cell[0..sz]));

    const right = try t.pageAlloc(.leaf);
    sz = makeLeafCell(&cell, "m", "2");
    try std.testing.expect(right.insertCell(0, cell[0..sz]));
    sz = makeLeafCell(&cell, "z", "3");
    try std.testing.expect(right.insertCell(1, cell[0..sz]));

    const root = try t.pageAlloc(.internal);
    root.setLink(t.pgnoOf(left));
    sz = makeInternalCell(&cell, t.pgnoOf(right), "m");
    try std.testing.expect(root.insertCell(0, cell[0..sz]));
    t.root = t.pgnoOf(root);
    t.poolUnpin(left, true);
    t.poolUnpin(right, true);
    t.poolUnpin(root, true);

    var buf: [MAX_VAL]u8 = undefined;
    try std.testing.expectEqualStrings("1", (try t.get("a", &buf)).?);
    try std.testing.expectEqualStrings("2", (try t.get("m", &buf)).?);
    try std.testing.expectEqualStrings("3", (try t.get("z", &buf)).?);
    try std.testing.expectEqual(null, try t.get("b", &buf));
    try std.testing.expectEqual(null, try t.get("zz", &buf));

    var small: [0]u8 = undefined;
    try std.testing.expectError(error.NoSpaceLeft, t.get("a", &small));
    const long_key: [MAX_KEY + 1]u8 = @splat('k');
    try std.testing.expectError(error.KeyTooLarge, t.get(&long_key, &buf));

    var p: [MAX_DEPTH]PathEntry = undefined;
    var depth: usize = undefined;
    const leaf = try t.descend("z", &p, &depth);
    defer t.poolUnpin(leaf, false);
    try std.testing.expectEqual(1, depth);
    try std.testing.expectEqual(t.root, p[0].pgno);
    try std.testing.expectEqual(1, p[0].idx);
    try std.testing.expectEqual(t.pgnoOf(right), p[1].pgno);
    try std.testing.expectEqual(1, t.poolPinned());
}

test CellList {
    var buf: [PAGE_SIZE]u8 = undefined;
    var cell: [PAGE_SIZE]u8 = undefined;
    const p: Page = .{ .page = &buf };
    p.init(.leaf);

    const keys = [_][]const u8{ "a", "b", "c", "d" };
    for (keys, 0..) |k, i| {
        const sz = makeLeafCell(&cell, k, "value");
        try std.testing.expect(p.insertCell(i, cell[0..sz]));
    }

    var cl: CellList = .{};
    cl.addPage(p);
    try std.testing.expectEqual(4, cl.n);
    try std.testing.expectEqual(4 * (4 + 1 + 5 + 2), cl.bytes(0, cl.n));

    // The list keeps copies, so a change to the page does not change the list.
    p.init(.leaf);
    const split = cl.chooseSplit(true);
    try std.testing.expectEqual(2, split);
    p.fill(.leaf, 0, &cl, 0, split);
    try std.testing.expectEqual(2, p.getN());
    try std.testing.expectEqualStrings("a", p.getCellKey(0));
    try std.testing.expectEqualStrings("b", p.getCellKey(1));

    // An internal split moves the middle cell up, so it is in neither half.
    cl.reset();
    try std.testing.expectEqual(0, cl.n);
    const q: Page = .{ .page = &cell };
    q.init(.internal);
    for (keys, 0..) |k, i| {
        var tmp: [16]u8 = undefined;
        const sz = makeInternalCell(&tmp, @intCast(i + 10), k);
        try std.testing.expect(q.insertCell(i, tmp[0..sz]));
    }
    cl.addPage(q);
    try std.testing.expectEqual(1, cl.chooseSplit(false));
}
