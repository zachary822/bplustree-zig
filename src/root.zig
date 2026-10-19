const std = @import("std");
const build_options = @import("build_options");
const Io = std.Io;
const Allocator = std.mem.Allocator;

const page_size = build_options.page_size;
const pool_frames = build_options.pool_frames;

/// The maximum length of a key.
pub const max_key = page_size / 16;
/// The maximum length of a value. A buffer of this size can hold all values that `get` returns.
pub const max_val = page_size / 8;
const max_depth = 32;

const hdr_size = 12;
const capacity = page_size - hdr_size;
const min_fill = capacity / 4;
/// The largest separator cell, with its slot, that a split sends to a parent.
const max_sep = max_key + 6 + 2;

comptime {
    std.debug.assert(page_size >= 256 and page_size <= 32768);
}

const meta_pgno = 0;
const magic = "BPTDISK1";

/// The errors that the tree gives, in addition to the I/O errors.
pub const Error = error{ BadFile, KeyTooLarge, ValueTooLarge, PoolExhausted, NoSpaceLeft };

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

/// A stack that keeps at most `cap` items inline.
fn Stack(comptime T: type, comptime cap: usize) type {
    return struct {
        buf: [cap]T = undefined,
        len: usize = 0,

        const Self = @This();

        fn push(self: *Self, v: T) void {
            self.buf[self.len] = v;
            self.len += 1;
        }

        fn pop(self: *Self) ?T {
            if (self.len == 0) return null;
            self.len -= 1;
            return self.buf[self.len];
        }

        fn items(self: *const Self) []const T {
            return self.buf[0..self.len];
        }
    };
}

const Frame = struct {
    /// The page in this frame, or null if the frame is free.
    pgno: ?u32 = null,
    pins: u32 = 0,
    dirty: bool = false,
    last_used: u64 = 0,
};

/// The buffer pool: a fixed set of frames that keep pages of the file in memory.
const Pool = struct {
    io: Io,
    file: Io.File,
    frames: [pool_frames]Frame = @splat(.{}),
    mem: []u8,
    tick: u64 = 0,
    reads: u64 = 0,
    writes: u64 = 0,

    const Load = enum { load, no_load };
    const Unpin = enum { clean, dirty };

    fn deinit(self: *Pool, gpa: Allocator) void {
        std.debug.assert(self.pinned() == 0);
        gpa.free(self.mem);
    }

    fn read(self: *Pool, pgno: u32, buf: *[page_size]u8) !void {
        const n = try self.file.readPositionalAll(self.io, buf, @as(u64, pgno) * page_size);
        if (n < page_size) @memset(buf[n..], 0);
        self.reads += 1;
    }

    fn write(self: *Pool, pgno: u32, buf: *const [page_size]u8) !void {
        try self.file.writePositionalAll(self.io, buf, @as(u64, pgno) * page_size);
        self.writes += 1;
    }

    fn frameData(self: *Pool, f: usize) *[page_size]u8 {
        return self.mem[page_size * f ..][0..page_size];
    }

    fn frameOf(self: *Pool, p: Page) *Frame {
        return &self.frames[(@intFromPtr(p.page) - @intFromPtr(self.mem.ptr)) / page_size];
    }

    fn find(self: *Pool, pgno: u32) ?usize {
        for (self.frames, 0..) |fr, f| {
            if (fr.pgno == pgno) return f;
        }
        return null;
    }

    fn touch(self: *Pool, fr: *Frame) void {
        self.tick += 1;
        fr.last_used = self.tick;
    }

    fn victim(self: *Pool) !usize {
        var best: ?usize = null;
        for (&self.frames, 0..) |*fr, f| {
            if (fr.pgno == null) return f;
            if (fr.pins == 0 and (best == null or fr.last_used < self.frames[best.?].last_used))
                best = f;
        }
        const f = best orelse return error.PoolExhausted;
        const fr = &self.frames[f];
        if (fr.dirty) try self.write(fr.pgno.?, self.frameData(f));
        fr.* = .{};
        return f;
    }

    fn pin(self: *Pool, pgno: u32, mode: Load) !Page {
        std.debug.assert(pgno != meta_pgno);
        if (self.find(pgno)) |f| {
            const fr = &self.frames[f];
            fr.pins += 1;
            self.touch(fr);
            return .{ .page = self.frameData(f) };
        }
        const f = try self.victim();
        if (mode == .load) try self.read(pgno, self.frameData(f));
        self.frames[f] = .{ .pgno = pgno, .pins = 1 };
        self.touch(&self.frames[f]);
        return .{ .page = self.frameData(f) };
    }

    fn unpin(self: *Pool, p: Page, mode: Unpin) void {
        const fr = self.frameOf(p);
        std.debug.assert(fr.pgno != null and fr.pins > 0);
        fr.pins -= 1;
        if (mode == .dirty) fr.dirty = true;

        if (build_options.pool_paranoid and fr.pins == 0) {
            if (fr.dirty) self.write(fr.pgno.?, p.page) catch |err| std.debug.panic("unpin: {t}", .{err});
            fr.* = .{};
            @memset(p.page, 0xAA);
        }
    }

    /// Pins a page that an operation holds. It does no I/O, so it cannot fail.
    fn pinHeld(self: *Pool, pgno: u32) Page {
        const p = self.heldPage(pgno);
        const fr = self.frameOf(p);
        fr.pins += 1;
        self.touch(fr);
        return p;
    }

    /// Gives a page that an operation holds, without a change to its pins.
    fn heldPage(self: *Pool, pgno: u32) Page {
        const f = self.find(pgno) orelse @panic("page is not held");
        std.debug.assert(self.frames[f].pins > 0);
        return .{ .page = self.frameData(f) };
    }

    fn markDirty(self: *Pool, p: Page) void {
        self.frameOf(p).dirty = true;
    }

    fn pgnoOf(self: *Pool, p: Page) u32 {
        return self.frameOf(p).pgno.?;
    }

    fn flush(self: *Pool) !void {
        for (&self.frames, 0..) |*fr, f| {
            if (fr.dirty) {
                try self.write(fr.pgno.?, self.frameData(f));
                fr.dirty = false;
            }
        }
    }

    fn pinned(self: *const Pool) usize {
        var n: usize = 0;
        for (self.frames) |fr| n += fr.pins;
        return n;
    }
};

const PathEntry = struct {
    pgno: u32,
    idx: usize,
};

/// The pages from the root to a leaf, which `descend` holds.
const Path = struct {
    entries: [max_depth]PathEntry = undefined,
    /// The level of the leaf.
    depth: usize = 0,
    leaf: Page = undefined,

    fn slice(self: *const Path) []const PathEntry {
        return self.entries[0 .. self.depth + 1];
    }
};

pub fn BPTree(comptime K: type, comptime V: type) type {
    return struct {
        const Self = @This();

        pool: Pool,
        root: u32 = 0,
        npages: u32 = 0,
        freelist: u32 = 0,
        /// Pages that an operation keeps pinned, so that a later access to them does no I/O.
        held: Stack(Page, 2 * max_depth) = .{},
        /// Pages that an operation allocates before it changes the tree.
        spare: Stack(Page, max_depth + 2) = .{},
        /// The cells of the pages that a split or a merge changes.
        scratch: *CellList,

        /// Opens the tree in `file`, which must be open for read and write. If the file is empty, it makes an empty tree.
        /// The caller owns `file` and must keep it open until `deinit`.
        pub fn init(gpa: Allocator, io: Io, file: Io.File) !Self {
            const mem = try gpa.alloc(u8, page_size * pool_frames);
            errdefer gpa.free(mem);
            const scratch = try gpa.create(CellList);
            errdefer gpa.destroy(scratch);
            scratch.* = .{};
            var t: Self = .{ .pool = .{ .io = io, .file = file, .mem = mem }, .scratch = scratch };

            if (try file.length(io) == 0) {
                t.npages = 1;
                const root = try t.pageAlloc(.leaf);
                t.root = t.pool.pgnoOf(root);
                t.pool.unpin(root, .dirty);
            } else {
                try t.metaRead();
            }

            return t;
        }

        /// Releases the memory. It does not close the file. Changes that `sync` did not write are lost.
        pub fn deinit(self: *Self, gpa: Allocator) void {
            self.pool.deinit(gpa);
            gpa.destroy(self.scratch);
        }

        /// Writes all changed pages and the meta page, and then syncs the file.
        pub fn sync(self: *Self) !void {
            try self.pool.flush();
            try self.metaWrite();
            try self.pool.file.sync(self.pool.io);
        }

        fn metaWrite(self: *Self) !void {
            var buf: [page_size]u8 = @splat(0);
            @memcpy(buf[0..magic.len], magic);
            put32(buf[8..], @intCast(page_size));
            put32(buf[12..], self.root);
            put32(buf[16..], self.npages);
            put32(buf[20..], self.freelist);
            try self.pool.write(meta_pgno, &buf);
        }

        fn metaRead(self: *Self) !void {
            var buf: [page_size]u8 = undefined;
            try self.pool.read(meta_pgno, &buf);

            if (!std.mem.eql(u8, magic, buf[0..magic.len]) or get32(buf[8..]) != page_size) return error.BadFile;
            self.root = get32(buf[12..]);
            self.npages = get32(buf[16..]);
            self.freelist = get32(buf[20..]);
        }

        /// Pins page `pgno`. A page number that is not in the file means that the file is corrupt.
        fn getPage(self: *Self, pgno: u32) !Page {
            if (pgno == meta_pgno or pgno >= self.npages) return error.BadFile;
            return self.pool.pin(pgno, .load);
        }

        fn pageAlloc(self: *Self, t: Page.Type) !Page {
            if (self.freelist != 0) {
                const p = try self.getPage(self.freelist);
                if (p.kind() != .free) {
                    self.pool.unpin(p, .clean);
                    return error.BadFile;
                }
                self.freelist = p.link();
                p.init(t);
                return p;
            }
            const pgno = self.npages;
            self.npages += 1;
            errdefer self.npages -= 1;
            const p = try self.pool.pin(pgno, .no_load);
            p.init(t);
            return p;
        }

        fn pageFree(self: *Self, p: Page) void {
            const pgno = self.pool.pgnoOf(p);
            p.init(.free);
            p.setLink(self.freelist);
            self.freelist = pgno;
            self.pool.unpin(p, .dirty);
        }

        fn releaseHeld(self: *Self) void {
            while (self.held.pop()) |p| self.pool.unpin(p, .clean);
        }

        /// Allocates `n` pages before an operation changes the tree. `takeSpare` then gives them out without I/O.
        fn reserve(self: *Self, n: usize) !void {
            for (0..n) |_| self.spare.push(try self.pageAlloc(.free));
        }

        fn takeSpare(self: *Self, t: Page.Type) Page {
            const p = self.spare.pop().?;
            p.init(t);
            return p;
        }

        /// Frees the spare pages that the operation did not use. The reverse order puts the freelist back as it was.
        fn releaseSpares(self: *Self) void {
            while (self.spare.pop()) |p| self.pageFree(p);
        }

        /// The maximum number of new pages that a chain of splits needs when level `d` gets a cell.
        fn splitPages(self: *Self, path: []const PathEntry, d: usize, splits: bool) usize {
            if (!splits) return 0;
            var n: usize = 1;
            var k = d;
            while (k > 0) {
                k -= 1;
                if (self.pool.heldPage(path[k].pgno).freeBytes() >= max_sep) return n;
                n += 1;
            }
            return n + 1; // a new root
        }

        /// Holds the siblings that `rebalance` can use, from level `d` up.
        /// Returns the maximum number of new pages that its redistributions need.
        fn holdSiblings(self: *Self, path: []const PathEntry, d: usize) !usize {
            var spares: usize = 0;
            var k = d;
            while (k > 0) : (k -= 1) {
                const parent = self.pool.heldPage(path[k - 1].pgno);
                const idx = path[k - 1].idx;
                const sib = try self.getPage(parent.child(if (idx > 0) idx - 1 else idx + 1));
                self.held.push(sib);
                if (sib.kind() != self.pool.heldPage(path[k].pgno).kind()) return error.BadFile;
                spares = @max(spares, self.splitPages(path, k - 1, parent.freeBytes() < max_sep));
                // A merge or a redistribution at level k removes at most one separator from the parent.
                if (parent.usedBytes() >= min_fill + max_sep) break;
            }
            return spares;
        }

        /// Holds the path from the root to the leaf for `key` until `releaseHeld`.
        fn descend(self: *Self, key: []const u8) !Path {
            errdefer self.releaseHeld();
            var path: Path = .{};
            var pgno = self.root;
            while (true) {
                const p = try self.getPage(pgno);
                self.held.push(p);
                const e = &path.entries[path.depth];
                e.pgno = pgno;
                switch (p.kind()) {
                    .leaf => {
                        path.leaf = p;
                        return path;
                    },
                    .internal => {},
                    else => return error.BadFile,
                }
                e.idx = p.childIndex(key);
                pgno = p.child(e.idx);
                path.depth += 1;
                if (path.depth >= max_depth) return error.BadFile;
            }
        }

        pub fn get(self: *Self, key: []const u8, out: []u8) !?[]u8 {
            if (key.len > max_key) return error.KeyTooLarge;
            var pgno = self.root;
            for (0..max_depth) |_| {
                const p = try self.getPage(pgno);
                defer self.pool.unpin(p, .clean);
                switch (p.kind()) {
                    .internal => pgno = p.child(p.childIndex(key)),
                    .leaf => {
                        const r = p.search(key);
                        if (!r.found) return null;
                        const val = p.leafVal(r.index);
                        if (out.len < val.len) return error.NoSpaceLeft;
                        @memcpy(out[0..val.len], val);
                        return out[0..val.len];
                    },
                    else => error.BadFile,
                }
            }
            return error.BadFile;
        }

        /// true if split. The caller holds the path and reserves the new pages.
        fn insertUp(self: *Self, path: []const PathEntry, d: usize, idx: usize, c: []const u8) bool {
            const pgno = path[d].pgno;
            const p = self.pool.pinHeld(pgno);
            if (p.insertCell(idx, c)) {
                self.pool.unpin(p, .dirty);
                return false;
            }

            const cl = self.scratch;
            cl.reset();
            for (0..p.count()) |i| {
                if (i == idx) cl.add(c);
                cl.add(p.cell(i));
            }
            if (idx == p.count()) cl.add(c);

            const leaf = p.kind() == .leaf;
            const s = cl.chooseSplit(leaf);
            const right = self.takeSpare(p.kind());
            const right_pg = self.pool.pgnoOf(right);
            var sep_buf: [max_key + 6]u8 = undefined;
            const sep = if (leaf) blk: {
                right.fill(.leaf, p.link(), cl, s, cl.cells.len);
                p.fill(.leaf, right_pg, cl, 0, s);
                break :blk makeInternalCell(&sep_buf, right_pg, right.cellKey(0));
            } else blk: {
                const mid = cl.cells.items()[s];
                right.fill(.internal, get32(mid), cl, s + 1, cl.cells.len);
                p.fill(.internal, p.link(), cl, 0, s);
                break :blk makeInternalCell(&sep_buf, right_pg, mid[6..][0..get16(mid[4..])]);
            };
            self.pool.unpin(right, .dirty);
            self.pool.unpin(p, .dirty);

            if (d == 0) {
                const root = self.takeSpare(.internal);
                root.setLink(pgno);
                _ = root.insertCell(0, sep);
                self.root = self.pool.pgnoOf(root);
                self.pool.unpin(root, .dirty);
            } else {
                _ = self.insertUp(path, d - 1, path[d - 1].idx, sep);
            }
            return true;
        }

        pub fn put(self: *Self, key: []const u8, val: []const u8) !void {
            if (key.len > max_key) return error.KeyTooLarge;
            if (val.len > max_val) return error.ValueTooLarge;
            const path = try self.descend(key);
            defer self.releaseHeld();
            const leaf = path.leaf;
            defer self.releaseSpares();

            const r = leaf.search(key);
            const old_sz = if (r.found) leaf.cell(r.index).len + 2 else 0;
            const new_sz = 4 + key.len + val.len + 2;
            const splits = leaf.freeBytes() + old_sz < new_sz;
            var spares = self.splitPages(path.slice(), path.depth, splits);
            if (r.found and !splits and leaf.usedBytes() - old_sz + new_sz < min_fill)
                spares = @max(spares, try self.holdSiblings(path.slice(), path.depth));
            try self.reserve(spares);

            // Nothing below can fail, so the tree changes completely or not at all.
            if (r.found) {
                leaf.deleteCell(r.index);
                self.pool.markDirty(leaf);
            }
            var c: [4 + max_key + max_val]u8 = undefined;
            const split = self.insertUp(path.slice(), path.depth, r.index, makeLeafCell(&c, key, val));
            std.debug.assert(split == splits);
            if (r.found and !split)
                self.rebalance(path.slice(), path.depth);
        }

        /// The caller holds the path and the siblings, and reserves the new pages.
        fn rebalance(self: *Self, path: []const PathEntry, d: usize) void {
            const p = self.pool.pinHeld(path[d].pgno);

            if (d == 0) {
                if (p.kind() == .internal and p.count() == 0) {
                    self.root = p.link();
                    self.pageFree(p);
                } else {
                    self.pool.unpin(p, .clean);
                }
                return;
            }

            if (p.usedBytes() >= min_fill) {
                self.pool.unpin(p, .clean);
                return;
            }
            self.pool.unpin(p, .clean);

            const parent = self.pool.pinHeld(path[d - 1].pgno);
            const idx = path[d - 1].idx;
            const li = if (idx > 0) idx - 1 else idx;
            const sep_idx = li;
            const left = self.pool.pinHeld(parent.child(li));
            const right = self.pool.pinHeld(parent.child(li + 1));
            const leaf = left.kind() == .leaf;

            const cl = self.scratch;
            cl.reset();
            cl.addPage(left);
            if (!leaf) {
                const k = parent.cellKey(sep_idx);
                var c: [max_key + 6]u8 = undefined;
                cl.add(makeInternalCell(&c, right.link(), k));
            }
            cl.addPage(right);

            // merge into left
            if (cl.bytes(0, cl.cells.len) <= capacity) {
                const link = if (leaf) right.link() else left.link();
                left.fill(left.kind(), link, cl, 0, cl.cells.len);
                self.pageFree(right);
                self.pool.unpin(left, .dirty);
                parent.deleteCell(sep_idx);
                self.pool.unpin(parent, .dirty);
                self.rebalance(path, d - 1);
                return;
            }

            // split evenly
            const s = cl.chooseSplit(leaf);
            var sep_buf: [max_key + 6]u8 = undefined;
            const right_pg = self.pool.pgnoOf(right);
            const sep = if (leaf) blk: {
                left.fill(.leaf, right_pg, cl, 0, s);
                right.fill(.leaf, right.link(), cl, s, cl.cells.len);
                break :blk makeInternalCell(&sep_buf, right_pg, right.cellKey(0));
            } else blk: {
                const mid = cl.cells.items()[s];
                left.fill(.internal, left.link(), cl, 0, s);
                right.fill(.internal, get32(mid), cl, s + 1, cl.cells.len);
                break :blk makeInternalCell(&sep_buf, right_pg, mid[6..][0..get16(mid[4..])]);
            };
            self.pool.unpin(left, .dirty);
            self.pool.unpin(right, .dirty);
            parent.deleteCell(sep_idx);
            self.pool.unpin(parent, .dirty);

            if (!self.insertUp(path, d - 1, sep_idx, sep)) {
                self.rebalance(path, d - 1);
            }
        }

        pub fn delete(self: *Self, key: []const u8) !bool {
            if (key.len > max_key) return error.KeyTooLarge;
            const path = try self.descend(key);
            defer self.releaseHeld();
            const leaf = path.leaf;
            defer self.releaseSpares();

            const r = leaf.search(key);
            if (!r.found) return false;
            const old_sz = leaf.cell(r.index).len + 2;
            if (leaf.usedBytes() - old_sz < min_fill)
                try self.reserve(try self.holdSiblings(path.slice(), path.depth));

            // Nothing below can fail, so the tree changes completely or not at all.
            leaf.deleteCell(r.index);
            self.pool.markDirty(leaf);
            self.rebalance(path.slice(), path.depth);
            return true;
        }
    };
}

const Page = struct {
    page: *[page_size]u8,

    /// Non-exhaustive, because a corrupt file can contain any byte.
    const Type = enum(u8) {
        free = 0,
        leaf = 1,
        internal = 2,
        _,
    };

    fn init(self: Page, t: Type) void {
        @memset(self.page, 0);
        self.page[0] = @backingInt(t);
        self.setCellStart(page_size);
    }

    fn kind(self: Page) Type {
        return @fromBackingInt(self.page[0]);
    }

    fn count(self: Page) u16 {
        return get16(self.page[2..]);
    }
    fn cellStart(self: Page) u16 {
        return get16(self.page[4..]);
    }
    fn frag(self: Page) u16 {
        return get16(self.page[6..]);
    }
    fn link(self: Page) u32 {
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

    fn slot(self: Page, i: usize) u16 {
        return get16(self.page[hdr_size + 2 * i ..]);
    }
    fn setSlot(self: Page, i: usize, off: usize) void {
        put16(self.page[hdr_size + 2 * i ..], @intCast(off));
    }
    fn cellSize(self: Page, c: []const u8) usize {
        if (self.kind() == .leaf) return 4 + @as(usize, get16(c)) + get16(c[2..]);
        return 6 + @as(usize, get16(c[4..]));
    }
    fn cell(self: Page, i: usize) []const u8 {
        const c = self.page[self.slot(i)..];
        return c[0..self.cellSize(c)];
    }
    fn cellKey(self: Page, i: usize) []const u8 {
        const c = self.cell(i);
        if (self.kind() == .leaf) {
            const klen = get16(c);
            return c[4..][0..klen];
        } else {
            const klen = get16(c[4..]);
            return c[6..][0..klen];
        }
    }
    fn leafVal(self: Page, i: usize) []const u8 {
        const c = self.cell(i);
        const vlen = get16(c[2..4]);
        return c[4 + get16(c) ..][0..vlen];
    }

    fn child(self: Page, i: usize) u32 {
        return if (i == 0) self.link() else get32(self.cell(i - 1));
    }

    fn usedBytes(self: Page) usize {
        return capacity - (self.cellStart() - hdr_size - 2 * @as(usize, self.count())) - self.frag();
    }

    fn freeBytes(self: Page) usize {
        return capacity - self.usedBytes();
    }

    const SearchResult = struct {
        found: bool,
        index: usize,
    };
    fn search(self: Page, key: []const u8) SearchResult {
        const n = self.count();
        var lo: usize = 0;
        var hi: usize = n;
        while (lo < hi) {
            const mid = (lo + hi) / 2;
            if (std.mem.lessThan(u8, self.cellKey(mid), key)) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        const found = lo < n and std.mem.eql(u8, key, self.cellKey(lo));
        return .{ .found = found, .index = lo };
    }

    fn compact(self: Page) void {
        var tmp: [page_size]u8 = undefined;
        const tmp_page: Page = .{ .page = &tmp };
        @memcpy(&tmp, self.page);
        var top: usize = page_size;
        const n = self.count();
        for (0..n) |i| {
            const c = tmp_page.cell(i);
            top -= c.len;
            @memcpy(self.page[top..][0..c.len], c);
            self.setSlot(i, top);
        }
        self.setCellStart(top);
        self.setFrag(0);
    }

    fn insertCell(self: Page, idx: usize, c: []const u8) bool {
        if (self.freeBytes() < c.len + 2) return false;
        const n: usize = self.count();
        if (self.cellStart() - (hdr_size + 2 * n) < c.len + 2)
            self.compact();
        const off: usize = self.cellStart() - c.len;
        @memcpy(self.page[off..][0..c.len], c);
        self.setCellStart(off);

        const s = (2 * (n - idx));
        @memmove(self.page[hdr_size + 2 * (idx + 1) ..][0..s], self.page[hdr_size + 2 * idx ..][0..s]);
        self.setSlot(idx, off);
        self.setN(n + 1);
        return true;
    }

    fn deleteCell(self: Page, idx: usize) void {
        const n: usize = self.count();
        const off = self.slot(idx);
        const sz = self.cell(idx).len;
        if (off == self.cellStart()) {
            self.setCellStart(off + sz);
        } else {
            self.setFrag(self.frag() + sz);
        }
        const s = 2 * (n - idx - 1);
        @memmove(self.page[hdr_size + 2 * idx ..][0..s], self.page[hdr_size + 2 * (idx + 1) ..][0..s]);
        self.setN(n - 1);
    }

    fn childIndex(self: Page, key: []const u8) usize {
        const e = self.search(key);
        return if (e.found) e.index + 1 else e.index;
    }

    fn fill(self: Page, t: Type, link_pgno: u32, cl: *const CellList, from: usize, to: usize) void {
        self.init(t);
        self.setLink(link_pgno);
        for (cl.cells.items()[from..to], 0..) |c, i| {
            const ok = self.insertCell(i, c);
            std.debug.assert(ok);
        }
    }
};

fn makeLeafCell(out: []u8, k: []const u8, v: []const u8) []u8 {
    put16(out, @intCast(k.len));
    put16(out[2..], @intCast(v.len));
    @memcpy(out[4..][0..k.len], k);
    @memcpy(out[4 + k.len ..][0..v.len], v);
    return out[0 .. 4 + k.len + v.len];
}

fn makeInternalCell(out: []u8, child_pg: u32, k: []const u8) []u8 {
    put32(out, child_pg);
    put16(out[4..], @intCast(k.len));
    @memcpy(out[6..][0..k.len], k);
    return out[0 .. 6 + k.len];
}

const CellList = struct {
    cells: Stack([]const u8, page_size / 2) = .{},
    buf: [2 * page_size]u8 = undefined,
    used: usize = 0,

    fn reset(self: *CellList) void {
        self.cells.len = 0;
        self.used = 0;
    }

    fn add(self: *CellList, c: []const u8) void {
        const dst = self.buf[self.used..][0..c.len];
        @memcpy(dst, c);
        self.cells.push(dst);
        self.used += c.len;
    }

    fn addPage(self: *CellList, p: Page) void {
        for (0..p.count()) |i| self.add(p.cell(i));
    }

    fn bytes(self: *const CellList, from: usize, to: usize) usize {
        var b: usize = 0;
        for (self.cells.items()[from..to]) |c| b += c.len + 2;
        return b;
    }

    fn chooseSplit(self: *const CellList, leaf: bool) usize {
        const n = self.cells.len;
        std.debug.assert(n >= 2);
        var best: ?usize = null;
        var best_worst: usize = 0;
        const hi = if (leaf) n - 1 else n - 2;

        for (1..hi + 1) |s| {
            const l = self.bytes(0, s);
            const r = self.bytes(if (leaf) s else s + 1, n);
            const worst = @max(l, r);
            if (best == null or worst < best_worst) {
                best = s;
                best_worst = worst;
            }
        }

        std.debug.assert(best != null and best_worst <= capacity);
        return best.?;
    }
};

fn createTestFile(dir: Io.Dir) !Io.File {
    return dir.createFile(std.testing.io, "test.bin", .{ .read = true });
}

test BPTree {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);

    try t.metaWrite();
    try t.metaRead();
}

test "BPTree sync and reopen" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var kbuf: [16]u8 = undefined;
    var out: [max_val]u8 = undefined;
    const N = 500;
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    {
        var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
        defer t.deinit(std.testing.allocator);
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        try t.sync();
    }
    // A new tree has an empty pool, so it reads all pages from the file.
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);
    for (0..N) |i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        try std.testing.expectEqualStrings("value", (try t.get(k, &out)).?);
    }
}

test "BPTree bad file" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    try file.writePositionalAll(io, "garbage!", 0);
    try std.testing.expectError(error.BadFile, BPTree.init(std.testing.allocator, io, file));
}

test Page {
    var buf: [page_size]u8 = undefined;
    var cell: [page_size]u8 = undefined;

    const leaf: Page = .{ .page = &buf };
    leaf.init(.leaf);
    try std.testing.expectEqual(.leaf, leaf.kind());
    try std.testing.expectEqual(capacity, leaf.freeBytes());

    const keys = [_][]const u8{ "delta", "alpha", "charlie", "bravo" };
    for (keys) |k| {
        const c = makeLeafCell(&cell, k, "value");
        const r = leaf.search(k);
        try std.testing.expect(!r.found);
        try std.testing.expect(leaf.insertCell(r.index, c));
    }
    try std.testing.expectEqual(4, leaf.count());
    try std.testing.expectEqualStrings("alpha", leaf.cellKey(0));
    try std.testing.expectEqualStrings("delta", leaf.cellKey(3));
    try std.testing.expectEqualStrings("value", leaf.leafVal(2));

    const r = leaf.search("alpha");
    try std.testing.expect(r.found);
    leaf.deleteCell(r.index);
    try std.testing.expectEqual(3, leaf.count());
    try std.testing.expect(leaf.frag() > 0);

    const used = leaf.usedBytes();
    leaf.compact();
    try std.testing.expectEqual(0, leaf.frag());
    try std.testing.expectEqual(used, leaf.usedBytes());
    try std.testing.expectEqualStrings("bravo", leaf.cellKey(0));
    try std.testing.expectEqualStrings("charlie", leaf.cellKey(1));
    try std.testing.expectEqualStrings("delta", leaf.cellKey(2));

    // Fill the page; insertCell must compact the fragmented space before it gives up.
    var i: usize = 0;
    while (true) : (i += 1) {
        var kbuf: [8]u8 = undefined;
        const k = std.fmt.bufPrint(&kbuf, "k{d:0>6}", .{i}) catch unreachable;
        if (!leaf.insertCell(leaf.search(k).index, makeLeafCell(&cell, k, "v"))) break;
    }
    try std.testing.expect(leaf.freeBytes() < 4 + 7 + 1 + 2);

    const internal: Page = .{ .page = &buf };
    internal.init(.internal);
    internal.setLink(7);
    try std.testing.expect(internal.insertCell(0, makeInternalCell(&cell, 9, "mid")));
    try std.testing.expectEqual(7, internal.child(0));
    try std.testing.expectEqual(9, internal.child(1));
    try std.testing.expectEqualStrings("mid", internal.cellKey(0));
}

test Pool {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);

    t.npages = pool_frames + 4;
    for (1..t.npages) |pg| {
        const p = try t.pool.pin(@intCast(pg), .no_load);
        p.init(.leaf);
        try std.testing.expectEqual(pg, t.pool.pgnoOf(p));
        t.pool.unpin(p, .dirty);
    }
    try std.testing.expectEqual(0, t.pool.pinned());

    const p = try t.getPage(1);
    try std.testing.expectEqual(.leaf, p.kind());
    t.pool.unpin(p, .clean);
    try std.testing.expectEqual(0, t.pool.pinned());
    try t.pool.flush();
}

test "BPTree page alloc" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);

    // open allocates the root leaf as page 1.
    try std.testing.expectEqual(1, t.root);
    try std.testing.expectEqual(2, t.npages);

    const a = try t.pageAlloc(.leaf);
    const a_pgno = t.pool.pgnoOf(a);
    try std.testing.expectEqual(2, a_pgno);
    try std.testing.expectEqual(.leaf, a.kind());
    try std.testing.expectEqual(3, t.npages);

    t.pageFree(a);
    try std.testing.expectEqual(a_pgno, t.freelist);

    const b = try t.pageAlloc(.internal);
    try std.testing.expectEqual(a_pgno, t.pool.pgnoOf(b));
    try std.testing.expectEqual(.internal, b.kind());
    try std.testing.expectEqual(0, t.freelist);
    try std.testing.expectEqual(3, t.npages);
    t.pool.unpin(b, .dirty);
    try std.testing.expectEqual(0, t.pool.pinned());
}

test "BPTree get" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);

    // Make a two-level tree by hand: the root holds "m", with "a" on the left and "m", "z" on the right.
    var cell: [page_size]u8 = undefined;
    const left = try t.getPage(t.root);
    try std.testing.expect(left.insertCell(0, makeLeafCell(&cell, "a", "1")));

    const right = try t.pageAlloc(.leaf);
    try std.testing.expect(right.insertCell(0, makeLeafCell(&cell, "m", "2")));
    try std.testing.expect(right.insertCell(1, makeLeafCell(&cell, "z", "3")));

    const root = try t.pageAlloc(.internal);
    root.setLink(t.pool.pgnoOf(left));
    try std.testing.expect(root.insertCell(0, makeInternalCell(&cell, t.pool.pgnoOf(right), "m")));
    t.root = t.pool.pgnoOf(root);
    t.pool.unpin(left, .dirty);
    t.pool.unpin(right, .dirty);
    t.pool.unpin(root, .dirty);

    var buf: [max_val]u8 = undefined;
    try std.testing.expectEqualStrings("1", (try t.get("a", &buf)).?);
    try std.testing.expectEqualStrings("2", (try t.get("m", &buf)).?);
    try std.testing.expectEqualStrings("3", (try t.get("z", &buf)).?);
    try std.testing.expectEqual(null, try t.get("b", &buf));
    try std.testing.expectEqual(null, try t.get("zz", &buf));

    var small: [0]u8 = undefined;
    try std.testing.expectError(error.NoSpaceLeft, t.get("a", &small));
    const long_key: [max_key + 1]u8 = @splat('k');
    try std.testing.expectError(error.KeyTooLarge, t.get(&long_key, &buf));

    const path = try t.descend("z");
    defer t.releaseHeld();
    try std.testing.expectEqual(1, path.depth);
    try std.testing.expectEqual(t.root, path.entries[0].pgno);
    try std.testing.expectEqual(1, path.entries[0].idx);
    try std.testing.expectEqual(t.pool.pgnoOf(right), path.entries[1].pgno);
    try std.testing.expectEqual(t.pool.pgnoOf(right), t.pool.pgnoOf(path.leaf));
    // descend holds the root and the leaf.
    try std.testing.expectEqual(2, t.pool.pinned());
}

test CellList {
    var buf: [page_size]u8 = undefined;
    var cell: [page_size]u8 = undefined;
    const p: Page = .{ .page = &buf };
    p.init(.leaf);

    const keys = [_][]const u8{ "a", "b", "c", "d" };
    for (keys, 0..) |k, i| {
        try std.testing.expect(p.insertCell(i, makeLeafCell(&cell, k, "value")));
    }

    var cl: CellList = .{};
    cl.addPage(p);
    try std.testing.expectEqual(4, cl.cells.len);
    try std.testing.expectEqual(4 * (4 + 1 + 5 + 2), cl.bytes(0, cl.cells.len));

    // The list keeps copies, so a change to the page does not change the list.
    p.init(.leaf);
    const split = cl.chooseSplit(true);
    try std.testing.expectEqual(2, split);
    p.fill(.leaf, 0, &cl, 0, split);
    try std.testing.expectEqual(2, p.count());
    try std.testing.expectEqualStrings("a", p.cellKey(0));
    try std.testing.expectEqualStrings("b", p.cellKey(1));

    // An internal split moves the middle cell up, so it is in neither half.
    cl.reset();
    try std.testing.expectEqual(0, cl.cells.len);
    const q: Page = .{ .page = &cell };
    q.init(.internal);
    for (keys, 0..) |k, i| {
        var tmp: [16]u8 = undefined;
        try std.testing.expect(q.insertCell(i, makeInternalCell(&tmp, @intCast(i + 10), k)));
    }
    cl.addPage(q);
    try std.testing.expectEqual(1, cl.chooseSplit(false));
}

test "BPTree put get delete" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);

    const N = 2000;
    var order: [N]usize = undefined;
    for (&order, 0..) |*o, i| o.* = i;
    var prng: std.Random.DefaultPrng = .init(42);
    prng.random().shuffle(usize, &order);

    var kbuf: [16]u8 = undefined;
    var vbuf: [32]u8 = undefined;
    var out: [max_val]u8 = undefined;

    for (order) |i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        const v = try std.fmt.bufPrint(&vbuf, "value-{d}-xxxxxxxxxxxxxxxx", .{i});
        try t.put(k, v);
    }
    try std.testing.expectEqual(0, t.pool.pinned());
    try std.testing.expect(t.npages > 2);

    // Replace the values of the even keys.
    for (0..N) |i| {
        if (i % 2 != 0) continue;
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        try t.put(k, "new");
    }
    for (0..N) |i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        const got = (try t.get(k, &out)).?;
        if (i % 2 == 0) {
            try std.testing.expectEqualStrings("new", got);
        } else {
            const v = try std.fmt.bufPrint(&vbuf, "value-{d}-xxxxxxxxxxxxxxxx", .{i});
            try std.testing.expectEqualStrings(v, got);
        }
    }

    prng.random().shuffle(usize, &order);
    for (order, 0..) |i, n| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        try std.testing.expect(try t.delete(k));
        try std.testing.expect(!try t.delete(k));
        try std.testing.expectEqual(null, try t.get(k, &out));
        if (n % 97 == 0) {
            for (order[n + 1 ..]) |j| {
                const kj = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{j});
                try std.testing.expect((try t.get(kj, &out)) != null);
            }
        }
    }
    try std.testing.expectEqual(0, t.pool.pinned());

    const root = try t.getPage(t.root);
    defer t.pool.unpin(root, .clean);
    try std.testing.expectEqual(.leaf, root.kind());
    try std.testing.expectEqual(0, root.count());
}

test "BPTree failed operation does not change the tree" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file);
    defer t.deinit(std.testing.allocator);

    var kbuf: [16]u8 = undefined;
    var out: [max_val]u8 = undefined;
    const big: [max_val]u8 = @splat('v');

    var n: usize = 0;
    while (t.npages < 2 * pool_frames + 2 * max_depth) : (n += 1) {
        try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{n}), &big);
    }

    // Pin pages that are not on the path of `key` and are not siblings of it,
    // so that only the path fits in the pool.
    const Pinner = struct {
        fn pinAllBut(tree: *BPTree, key: []const u8, pinned: *[pool_frames]Page) !usize {
            const path = try tree.descend(key);
            defer tree.releaseHeld();
            const p = path.slice();
            var skip: Stack(u32, 2 * max_depth) = .{};
            for (p, 0..) |e, k| {
                skip.push(e.pgno);
                if (k == 0) continue;
                const parent = tree.pool.heldPage(p[k - 1].pgno);
                const idx = p[k - 1].idx;
                skip.push(parent.child(if (idx > 0) idx - 1 else idx + 1));
            }
            var count: usize = 0;
            var pg: u32 = 1;
            while (count < pool_frames - p.len) : (pg += 1) {
                if (std.mem.indexOfScalar(u32, skip.items(), pg) != null) continue;
                pinned[count] = try tree.getPage(pg);
                count += 1;
            }
            return count;
        }
        fn unpinAll(tree: *BPTree, pinned: []const Page) void {
            for (pinned) |p| tree.pool.unpin(p, .clean);
        }
    };
    var pinned: [pool_frames]Page = undefined;

    // A put that must split fails before it changes the tree.
    var failed_puts: usize = 0;
    for (0..n) |i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}x", .{i});
        const count = try Pinner.pinAllBut(&t, k, &pinned);
        const npages = t.npages;
        const freelist = t.freelist;
        const root = t.root;
        const result = t.put(k, &big);
        try std.testing.expectEqual(count, t.pool.pinned());
        Pinner.unpinAll(&t, pinned[0..count]);
        if (result) |_| continue else |err| try std.testing.expectEqual(error.PoolExhausted, err);
        failed_puts += 1;
        try std.testing.expectEqual(null, try t.get(k, &out));
        try std.testing.expectEqual(npages, t.npages);
        try std.testing.expectEqual(freelist, t.freelist);
        try std.testing.expectEqual(root, t.root);
        // The same put works when the pool has space.
        try t.put(k, &big);
        try std.testing.expectEqualStrings(&big, (try t.get(k, &out)).?);
    }
    try std.testing.expect(failed_puts > 0);

    // A delete that must rebalance fails before it changes the tree.
    var failed_deletes: usize = 0;
    for (0..2 * n) |j| {
        const k = if (j % 2 == 0)
            try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{j / 2})
        else
            try std.fmt.bufPrint(&kbuf, "key{d:0>8}x", .{j / 2});
        const count = try Pinner.pinAllBut(&t, k, &pinned);
        const result = t.delete(k);
        try std.testing.expectEqual(count, t.pool.pinned());
        Pinner.unpinAll(&t, pinned[0..count]);
        if (result) |found| {
            try std.testing.expect(found);
            continue;
        } else |err| try std.testing.expectEqual(error.PoolExhausted, err);
        failed_deletes += 1;
        try std.testing.expectEqualStrings(&big, (try t.get(k, &out)).?);
        try std.testing.expect(try t.delete(k));
    }
    try std.testing.expect(failed_deletes > 0);

    for (0..n) |i| {
        try std.testing.expectEqual(null, try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out));
        try std.testing.expectEqual(null, try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}x", .{i}), &out));
    }
    try std.testing.expectEqual(0, t.pool.pinned());
    const root = try t.getPage(t.root);
    defer t.pool.unpin(root, .clean);
    try std.testing.expectEqual(.leaf, root.kind());
    try std.testing.expectEqual(0, root.count());
}
