const std = @import("std");
const build_options = @import("build_options");
const Io = std.Io;
const Allocator = std.mem.Allocator;

const page_size = build_options.page_size;
const pool_frames = build_options.pool_frames;
const max_usage = build_options.max_usage;

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
const magic = "BPTWAL01";
const meta_size = 32;
const max_log_bytes = 10 << 20;

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

const State = packed struct(u32) {
    pins: u24 = 0,
    usage: u4 = 0,
    mapped: bool = false,
    valid: bool = false,
    dirty: bool = false,
    io: bool = false,
};

comptime {
    std.debug.assert(max_usage <= std.math.maxInt(u4));
}

const Frame = struct {
    state: std.atomic.Value(u32) align(std.atomic.cache_line) = .init(0),
    pgno: ?u32 = null,
    lsn: std.atomic.Value(u64) = .init(0),

    fn load(self: *const Frame) State {
        return @bitCast(self.state.load(.acquire));
    }

    fn cas(self: *Frame, old: State, new: State) ?State {
        const found = self.state.cmpxchgWeak(@bitCast(old), @bitCast(new), .acq_rel, .acquire) orelse return null;
        return @bitCast(found);
    }
};

const Wal = struct {
    file: Io.File,
    mu: Io.Mutex = .init,
    end: std.atomic.Value(u64) = .init(0),
    durable: std.atomic.Value(u64) = .init(0),
    sync_mu: Io.Mutex = .init,
    syncing: bool = false,
    synced: Io.Condition = .init,
    syncs: std.atomic.Value(u64) = .init(0),
    epoch: u32 = 0,

    const rec_hdr = 16;

    const Kind = enum(u8) {
        page = 1,
        commit = 2,
        _,
    };

    const Record = struct {
        kind: Kind,
        arg: u32,
        end: u64,
    };

    fn header(buf: *[rec_hdr]u8, epoch: u32, kind: Kind, arg: u32) void {
        put32(buf[4..], epoch);
        buf[8] = @backingInt(kind);
        @memset(buf[9..12], 0);
        put32(buf[12..], arg);
    }

    fn crc(rec: []const u8) u32 {
        return std.hash.Crc32.hash(rec[4..]);
    }

    fn append(self: *Wal, io: Io, pages: []const Page, root: u32) !u64 {
        self.mu.lockUncancelable(io);
        defer self.mu.unlock(io);
        var off = self.end.raw;
        var rec: [rec_hdr + page_size]u8 = undefined;
        for (pages) |p| {
            header(rec[0..rec_hdr], self.epoch, .page, p.pgno);
            @memcpy(rec[rec_hdr..], p.page);
            put32(&rec, crc(&rec));
            try self.file.writePositionalAll(io, &rec, off);
            off += rec.len;
        }
        header(rec[0..rec_hdr], self.epoch, .commit, root);
        put32(&rec, crc(rec[0..rec_hdr]));
        try self.file.writePositionalAll(io, rec[0..rec_hdr], off);
        off += rec_hdr;
        self.end.store(off, .release);
        return off;
    }

    fn flushTo(self: *Wal, io: Io, lsn: u64) !void {
        if (lsn <= self.durable.load(.acquire)) return;
        self.sync_mu.lockUncancelable(io);
        defer self.sync_mu.unlock(io);
        while (lsn > self.durable.load(.acquire)) {
            if (self.syncing) {
                self.synced.waitUncancelable(io, &self.sync_mu);
                continue;
            }
            self.syncing = true;
            const end = self.end.load(.acquire);
            self.sync_mu.unlock(io);
            const result = self.file.sync(io);
            self.sync_mu.lockUncancelable(io);
            self.syncing = false;
            self.synced.broadcast(io);
            try result;
            _ = self.syncs.fetchAdd(1, .monotonic);
            self.durable.store(end, .release);
        }
    }

    fn restart(self: *Wal, epoch: u32) void {
        self.epoch = epoch;
        self.end.store(0, .release);
        self.durable.store(0, .release);
    }

    fn next(self: *Wal, io: Io, off: u64, buf: *[page_size]u8) !?Record {
        var rec: [rec_hdr + page_size]u8 = undefined;
        if (try self.file.readPositionalAll(io, rec[0..rec_hdr], off) < rec_hdr) return null;
        if (get32(rec[4..]) != self.epoch) return null;
        const kind: Kind = @fromBackingInt(rec[8]);
        const len: usize = switch (kind) {
            .page => rec_hdr + page_size,
            .commit => rec_hdr,
            _ => return null,
        };
        if (len > rec_hdr and try self.file.readPositionalAll(io, rec[rec_hdr..len], off + rec_hdr) < len - rec_hdr)
            return null;
        if (get32(&rec) != crc(rec[0..len])) return null;
        if (kind == .page) @memcpy(buf, rec[rec_hdr..]);
        return .{ .kind = kind, .arg = get32(rec[12..]), .end = off + len };
    }
};

const table_parts = 128;

const Partition = struct {
    lock: Io.RwLock align(std.atomic.cache_line) = .init,
    map: std.AutoHashMapUnmanaged(u32, usize) = .empty,
};

/// The buffer pool: a fixed set of frames that keep pages of the file in memory.
const Pool = struct {
    io: Io,
    file: Io.File,
    wal: Wal,
    frames: [pool_frames]Frame = @splat(.{}),
    mem: []u8,
    table: [table_parts]Partition = @splat(.{}),
    hand: std.atomic.Value(u64) = .init(0),
    reads: std.atomic.Value(u64) = .init(0),
    writes: std.atomic.Value(u64) = .init(0),
    lookups: std.atomic.Value(u64) = .init(0),

    latches: [pool_frames]Io.RwLock = @splat(.init),
    locks: std.atomic.Value(u64) = .init(0),

    const Load = enum { load, no_load };
    const Unpin = union(enum) {
        clean,
        dirty,
        logged: u64,
    };

    fn initTable(self: *Pool, gpa: Allocator) !void {
        errdefer self.deinitTable(gpa);
        for (&self.table) |*part| try part.map.ensureTotalCapacity(gpa, pool_frames);
    }

    fn deinitTable(self: *Pool, gpa: Allocator) void {
        for (&self.table) |*part| part.map.deinit(gpa);
    }

    fn deinit(self: *Pool, gpa: Allocator) void {
        std.debug.assert(self.pinned() == 0);
        self.deinitTable(gpa);
        gpa.free(self.mem);
    }

    fn partition(self: *Pool, pgno: u32) *Partition {
        return &self.table[pgno % table_parts];
    }

    fn lockPart(self: *Pool, part: *Partition, mode: Latch) void {
        switch (mode) {
            .shared => part.lock.lockSharedUncancelable(self.io),
            .exclusive => part.lock.lockUncancelable(self.io),
        }
        _ = self.locks.fetchAdd(1, .monotonic);
    }

    fn read(self: *Pool, pgno: u32, buf: *[page_size]u8) !void {
        self.delay();
        const n = try self.file.readPositionalAll(self.io, buf, @as(u64, pgno) * page_size);
        if (n < page_size) @memset(buf[n..], 0);
        _ = self.reads.fetchAdd(1, .monotonic);
    }

    fn write(self: *Pool, pgno: u32, buf: *const [page_size]u8) !void {
        self.delay();
        try self.file.writePositionalAll(self.io, buf, @as(u64, pgno) * page_size);
        _ = self.writes.fetchAdd(1, .monotonic);
    }

    fn writeBack(self: *Pool, pgno: u32, lsn: u64, buf: *const [page_size]u8) !void {
        try self.wal.flushTo(self.io, lsn);
        try self.write(pgno, buf);
    }

    fn frameData(self: *Pool, f: usize) *[page_size]u8 {
        return self.mem[page_size * f ..][0..page_size];
    }

    fn frameIndex(self: *Pool, p: Page) usize {
        return (@intFromPtr(p.page) - @intFromPtr(self.mem.ptr)) / page_size;
    }

    fn latch(self: *Pool, p: Page, mode: Latch) void {
        const l = &self.latches[self.frameIndex(p)];
        switch (mode) {
            .shared => l.lockSharedUncancelable(self.io),
            .exclusive => l.lockUncancelable(self.io),
        }
    }

    fn tryLatch(self: *Pool, p: Page, mode: Latch) bool {
        const l = &self.latches[self.frameIndex(p)];
        return switch (mode) {
            .shared => l.tryLockShared(self.io),
            .exclusive => l.tryLock(self.io),
        };
    }

    fn unlatch(self: *Pool, p: Page, mode: Latch) void {
        const l = &self.latches[self.frameIndex(p)];
        switch (mode) {
            .shared => l.unlockShared(self.io),
            .exclusive => l.unlock(self.io),
        }
    }

    fn find(self: *Pool, pgno: u32) ?usize {
        const part = self.partition(pgno);
        self.lockPart(part, .shared);
        defer part.lock.unlockShared(self.io);
        return part.map.get(pgno);
    }

    fn pinFound(fr: *Frame) void {
        var s = fr.load();
        while (true) {
            var n = s;
            n.pins += 1;
            if (n.usage < max_usage) n.usage += 1;
            s = fr.cas(s, n) orelse return;
        }
    }

    fn unpinFrame(fr: *Frame, dirty: bool) State {
        var s = fr.load();
        while (true) {
            var n = s;
            n.pins -= 1;
            if (dirty) n.dirty = true;
            s = fr.cas(s, n) orelse return n;
        }
    }

    fn waitIo(self: *Pool, fr: *Frame) State {
        while (true) {
            const s = fr.load();
            if (!s.io) return s;
            self.io.futexWaitUncancelable(u32, &fr.state.raw, @bitCast(s));
        }
    }

    fn endIo(self: *Pool, fr: *Frame, valid: bool, clean: bool) void {
        var s = fr.load();
        while (true) {
            var n = s;
            n.io = false;
            if (valid) n.valid = true;
            if (clean) n.dirty = false;
            s = fr.cas(s, n) orelse break;
        }
        self.io.futexWake(u32, &fr.state.raw, std.math.maxInt(u32));
    }

    fn sweep(self: *Pool) !usize {
        var tries: usize = pool_frames;
        while (true) {
            const f: usize = @intCast(self.hand.fetchAdd(1, .monotonic) % pool_frames);
            const fr = &self.frames[f];
            var s = fr.load();
            while (true) {
                if (s.pins != 0) {
                    tries -= 1;
                    if (tries == 0) return error.PoolExhausted;
                    break;
                }
                var n = s;
                if (s.usage != 0) {
                    n.usage -= 1;
                    s = fr.cas(s, n) orelse {
                        tries = pool_frames;
                        break;
                    };
                } else {
                    n.pins = 1;
                    s = fr.cas(s, n) orelse return f;
                }
            }
        }
    }

    fn writeVictim(self: *Pool, f: usize) !bool {
        const fr = &self.frames[f];
        var s = fr.load();
        while (true) {
            if (s.pins != 1) return false;
            var n = s;
            n.io = true;
            s = fr.cas(s, n) orelse break;
        }
        const result = self.writeBack(fr.pgno.?, fr.lsn.load(.acquire), self.frameData(f));
        self.endIo(fr, false, if (result) |_| true else |_| false);
        try result;
        return true;
    }

    fn unmap(self: *Pool, f: usize) bool {
        const fr = &self.frames[f];
        const pgno = fr.pgno.?;
        const part = self.partition(pgno);
        self.lockPart(part, .exclusive);
        defer part.lock.unlock(self.io);
        var s = fr.load();
        while (true) {
            if (s.pins != 1 or s.dirty) return false;
            s = fr.cas(s, .{ .pins = 1 }) orelse break;
        }
        _ = part.map.remove(pgno);
        fr.pgno = null;
        return true;
    }

    fn victim(self: *Pool) !usize {
        while (true) {
            const f = try self.sweep();
            const fr = &self.frames[f];
            const s = fr.load();
            if (s.dirty) {
                const written = self.writeVictim(f) catch |err| {
                    _ = unpinFrame(fr, false);
                    return err;
                };
                if (!written) {
                    _ = unpinFrame(fr, false);
                    continue;
                }
            }
            if (s.mapped and !self.unmap(f)) {
                _ = unpinFrame(fr, false);
                continue;
            }
            return f;
        }
    }

    fn readFrame(self: *Pool, f: usize) !void {
        const fr = &self.frames[f];
        const result = self.read(fr.pgno.?, self.frameData(f));
        self.endIo(fr, if (result) |_| true else |_| false, false);
        return result;
    }

    fn ready(self: *Pool, f: usize) !Page {
        const fr = &self.frames[f];
        while (true) {
            const s = self.waitIo(fr);
            if (s.valid) break;
            var n = s;
            n.io = true;
            if (fr.cas(s, n) == null) {
                self.readFrame(f) catch |err| {
                    _ = unpinFrame(fr, false);
                    return err;
                };
                break;
            }
        }
        return .{ .page = self.frameData(f), .pgno = fr.pgno.? };
    }

    fn pin(self: *Pool, pgno: u32, mode: Load) !Page {
        std.debug.assert(pgno != meta_pgno);
        _ = self.lookups.fetchAdd(1, .monotonic);
        const part = self.partition(pgno);
        self.lockPart(part, .shared);
        if (part.map.get(pgno)) |f| {
            pinFound(&self.frames[f]);
            part.lock.unlockShared(self.io);
            return self.ready(f);
        }
        part.lock.unlockShared(self.io);

        const v = try self.victim();
        const fr = &self.frames[v];
        self.lockPart(part, .exclusive);
        const entry = part.map.getOrPutAssumeCapacity(pgno);
        if (entry.found_existing) {
            // another thread put the page in a frame while this one looked for a victime. the victim stays empty.
            _ = unpinFrame(fr, false);
            const f = entry.value_ptr.*;
            pinFound(&self.frames[f]);
            part.lock.unlock(self.io);
            return self.ready(f);
        }
        entry.value_ptr.* = v;
        fr.pgno = pgno;
        fr.lsn.store(0, .monotonic);

        fr.state.store(@bitCast(State{ .pins = 1, .usage = 1, .mapped = true, .valid = mode == .no_load, .io = mode == .load }), .release);
        part.lock.unlock(self.io);
        if (mode == .load) self.readFrame(v) catch |err| {
            _ = unpinFrame(fr, false);
            return err;
        };
        return .{ .page = self.frameData(v), .pgno = pgno };
    }

    fn unpin(self: *Pool, p: Page, mode: Unpin) void {
        const f = self.frameIndex(p);
        const fr = &self.frames[f];
        std.debug.assert(fr.load().pins > 0);
        if (mode == .logged) _ = fr.lsn.fetchMax(mode.logged, .release);
        const s = unpinFrame(fr, mode != .clean);
        if (build_options.pool_paranoid and s.pins == 0) self.drop(f);
    }

    fn drop(self: *Pool, f: usize) void {
        const fr = &self.frames[f];
        var s = fr.load();
        while (true) {
            if (s.pins != 0 or !s.mapped) return;
            var n = s;
            n.pins = 1;
            s = fr.cas(s, n) orelse break;
        }
        const written = !s.dirty or self.writeVictim(f) catch |err| std.debug.panic("unpin: {t}", .{err});
        if (written and self.unmap(f)) @memset(self.frameData(f), 0xAA);
        _ = unpinFrame(fr, false);
    }

    fn flush(self: *Pool) !void {
        for (&self.frames, 0..) |*fr, f| {
            if (!fr.load().dirty) continue;
            try self.write(fr.pgno.?, self.frameData(f));
            self.endIo(fr, false, true);
        }
    }

    fn pinned(self: *Pool) usize {
        var n: usize = 0;
        for (&self.frames) |*fr| n += fr.load().pins;
        return n;
    }

    fn delay(self: *Pool) void {
        if (build_options.disk_delay_us > 0)
            self.io.sleep(.fromMicroseconds(build_options.disk_delay_us), .awake) catch {};
    }
};

const PathEntry = struct {
    page: Page,
    idx: usize,
    sib: ?Page = null,
};

/// The pages from the root to a leaf, which `descend` holds.
const Path = struct {
    entries: [max_depth]PathEntry = undefined,
    /// The level of the leaf.
    depth: usize = 0,

    fn leaf(self: *const Path) Page {
        return self.entries[self.depth].page;
    }

    fn slice(self: *Path) []PathEntry {
        return self.entries[0 .. self.depth + 1];
    }
};

const Latch = enum { shared, exclusive };

const Held = struct {
    page: Page,
    mode: Latch,
};

const Descent = enum {
    read,
    optimistic,
    write,
};

const max_changed = 3 * max_depth + 2;

const Op = struct {
    held: Stack(Held, 2 * max_depth) = .{},
    top: usize = 0,
    root_latch: ?Latch = null,
    reserved: Stack(Page, max_depth + 2) = .{},
    spares: usize = 0,
    scratch: CellList = .{},
    changed: Stack(Page, max_changed) = .{},
    freed: Stack(Page, max_changed) = .{},
    lsn: u64 = 0,

    fn owns(op: *const Op, p: Page) bool {
        for (op.held.items()[op.top..]) |h| if (h.page.page == p.page) return true;
        for (op.reserved.items()) |r| if (r.page == p.page) return true;
        return false;
    }

    fn wrote(op: *const Op, p: Page) bool {
        for (op.changed.items()) |c| if (c.page == p.page) return true;
        for (op.freed.items()) |f| if (f.page == p.page) return true;
        return false;
    }
};

pub const BPTree = struct {
    pool: Pool,
    root: u32 = 0,
    npages: u32 = 0,
    freelist: u32 = 0,

    root_latch: Io.RwLock = .init,
    alloc_mu: Io.Mutex = .init,
    durable: bool = true,

    /// Opens the tree in `file`, which must be open for read and write. If the file is empty, it makes an empty tree.
    /// The caller owns `file` and must keep it open until `deinit`.
    pub fn init(gpa: Allocator, io: Io, file: Io.File, log: Io.File) !BPTree {
        const mem = try gpa.alloc(u8, page_size * pool_frames);
        errdefer gpa.free(mem);
        var t: BPTree = .{ .pool = .{ .io = io, .file = file, .wal = .{ .file = log }, .mem = mem } };
        try t.pool.initTable(gpa);
        errdefer t.pool.deinitTable(gpa);

        if (try file.length(io) == 0) {
            try log.setLength(io, 0);
            t.npages = 1;
            const root = try t.pageAlloc(.leaf);
            t.root = root.pgno;
            t.pool.unpin(root, .dirty);
            try t.sync();
        } else {
            try t.metaRead();
            try t.recover(gpa);
        }

        return t;
    }

    /// Releases the memory. It does not close the file. Changes that `sync` did not write are lost.
    pub fn deinit(self: *BPTree, gpa: Allocator) void {
        self.pool.deinit(gpa);
    }

    /// Writes all changed pages and the meta page, and then syncs the file.
    pub fn sync(self: *BPTree) !void {
        const io = self.pool.io;
        try self.pool.flush();
        try self.pool.file.sync(io);
        const epoch = self.pool.wal.epoch + 1;
        try self.metaWrite(epoch);
        try self.pool.file.sync(io);
        if (try self.pool.wal.file.length(io) > max_log_bytes)
            try self.pool.wal.file.setLength(io, 0);
        self.pool.wal.restart(epoch);
    }

    fn metaWrite(self: *BPTree, epoch: u32) !void {
        var buf: [meta_size]u8 = undefined;
        @memcpy(buf[0..magic.len], magic);
        put32(buf[8..], @intCast(page_size));
        put32(buf[12..], epoch);
        put32(buf[16..], self.root);
        put32(buf[20..], self.npages);
        put32(buf[24..], self.freelist);
        put32(buf[28..], std.hash.Crc32.hash(buf[0..28]));
        try self.pool.file.writePositionalAll(self.pool.io, &buf, epoch % 2 * (page_size / 2));
    }

    fn metaRead(self: *BPTree) !void {
        var page: [page_size]u8 = undefined;
        try self.pool.read(meta_pgno, &page);
        var best: ?[]const u8 = null;
        for ([_]usize{ 0, page_size / 2 }) |off| {
            const m = page[off..][0..meta_size];
            if (!std.mem.eql(u8, magic, m[0..magic.len]) or get32(m[8..]) != page_size) continue;
            if (get32(m[28..]) != std.hash.Crc32.hash(m[0..28])) continue;
            if (best == null or get32(m[12..]) > get32(best.?[12..])) best = m;
        }
        const m = best orelse return error.BadFile;
        self.pool.wal.epoch = get32(m[12..]);
        self.root = get32(m[16..]);
        self.npages = get32(m[20..]);
        self.freelist = get32(m[24..]);
    }

    fn recover(self: *BPTree, gpa: Allocator) !void {
        const io = self.pool.io;
        const wal = &self.pool.wal;
        var buf: [page_size]u8 = undefined;

        var off: u64 = 0;
        var committed: u64 = 0;
        var root = self.root;
        while (try wal.next(io, off, &buf)) |r| : (off = r.end) {
            if (r.kind != .commit) continue;
            committed = r.end;
            if (r.arg != 0) root = r.arg;
        }
        if (off == 0) return;

        off = 0;
        while (off < committed) {
            const r = (try wal.next(io, off, &buf)).?;
            if (r.kind == .page) {
                if (r.arg == meta_pgno) return error.BadFile;
                try self.pool.write(r.arg, &buf);
                self.npages = @max(self.npages, r.arg + 1);
            }
            off = r.end;
        }
        self.root = root;
        try self.rebuildFreeList(gpa);
        try self.sync();
    }

    fn rebuildFreeList(self: *BPTree, gpa: Allocator) !void {
        const seen = try gpa.alloc(bool, self.npages);
        defer gpa.free(seen);
        @memset(seen, false);
        try self.markReachable(seen, self.root, 0);
        self.freelist = 0;
        var pg = self.npages;
        while (pg > 1) {
            pg -= 1;
            if (seen[pg]) continue;
            const p = try self.pool.pin(pg, .no_load);
            p.init(.free);
            p.setLink(self.freelist);
            self.freelist = pg;
            self.pool.unpin(p, .dirty);
        }
    }

    fn markReachable(self: *BPTree, seen: []bool, pgno: u32, depth: usize) !void {
        if (pgno == meta_pgno or pgno >= self.npages or seen[pgno] or depth >= max_depth) return error.BadFile;
        seen[pgno] = true;
        const p = try self.getPage(pgno);
        defer self.pool.unpin(p, .clean);
        switch (p.kind()) {
            .leaf => {},
            .internal => for (0..p.count() + 1) |i| try self.markReachable(seen, p.child(i), depth + 1),
            else => return error.BadFile,
        }
    }

    /// Pins page `pgno`. A page number that is not in the file means that the file is corrupt.
    fn getPage(self: *BPTree, pgno: u32) !Page {
        if (pgno == meta_pgno or pgno >= @atomicLoad(u32, &self.npages, .monotonic)) return error.BadFile;
        return self.pool.pin(pgno, .load);
    }

    fn pageAlloc(self: *BPTree, t: Page.Kind) !Page {
        self.alloc_mu.lockUncancelable(self.pool.io);
        defer self.alloc_mu.unlock(self.pool.io);
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
        const p = try self.pool.pin(pgno, .no_load);
        @atomicStore(u32, &self.npages, pgno + 1, .monotonic);
        p.init(t);
        return p;
    }

    fn pageFree(self: *BPTree, op: *Op, p: Page) void {
        _ = self;
        std.debug.assert(op.owns(p));
        p.init(.free);
        op.freed.push(p);
    }

    fn changed(self: *BPTree, op: *Op, p: Page) void {
        _ = self;
        std.debug.assert(op.owns(p));
        for (op.changed.items()) |c| if (c.page == p.page) return;
        op.changed.push(p);
    }

    fn commit(self: *BPTree, op: *Op) void {
        if (op.changed.len > 0) {
            const root = if (op.root_latch == .exclusive) self.root else 0;
            op.lsn = self.pool.wal.append(self.pool.io, op.changed.items(), root) catch |err|
                std.debug.panic("commit: cannot write the log: {t}", .{err});
        }
        if (op.freed.len > 0) {
            self.alloc_mu.lockUncancelable(self.pool.io);
            for (op.freed.items()) |p| {
                p.setLink(self.freelist);
                self.freelist = p.pgno;
            }
            self.alloc_mu.unlock(self.pool.io);
        }
    }

    fn finish(self: *BPTree, op: *Op) void {
        self.commit(op);
        while (op.reserved.pop()) |p| self.unpinOwned(op, p);
        self.releaseHeld(op);
        op.changed.len = 0;
        op.freed.len = 0;
    }

    fn lockRoot(self: *BPTree, op: *Op, mode: Latch) void {
        switch (mode) {
            .shared => self.root_latch.lockSharedUncancelable(self.pool.io),
            .exclusive => self.root_latch.lockUncancelable(self.pool.io),
        }
        op.root_latch = mode;
    }

    fn unlockRoot(self: *BPTree, op: *Op) void {
        const mode = op.root_latch orelse return;
        switch (mode) {
            .shared => self.root_latch.unlockShared(self.pool.io),
            .exclusive => self.root_latch.unlock(self.pool.io),
        }
        op.root_latch = null;
    }

    fn release(self: *BPTree, op: *const Op, h: Held) void {
        self.pool.unlatch(h.page, h.mode);
        self.unpinOwned(op, h.page);
    }

    fn unpinOwned(self: *BPTree, op: *const Op, p: Page) void {
        self.pool.unpin(p, if (op.wrote(p)) .{ .logged = op.lsn } else .clean);
    }

    fn releaseAbove(self: *BPTree, op: *Op) void {
        self.unlockRoot(op);
        const last = op.held.len - 1;
        for (op.held.items()[op.top..last]) |h| self.release(op, h);
        op.top = last;
    }

    fn releaseHeld(self: *BPTree, op: *Op) void {
        self.unlockRoot(op);
        while (op.held.len > op.top) self.release(op, op.held.pop().?);
        op.held.len = 0;
        op.top = 0;
    }

    /// Allocates `n` pages before an operation changes the tree. `takeSpare` then gives them out without I/O.
    fn reserve(self: *BPTree, op: *Op, n: usize) !void {
        std.debug.assert(op.spares == op.reserved.len);
        for (0..n) |_| {
            op.reserved.push(try self.pageAlloc(.free));
            op.spares += 1;
        }
    }

    fn takeSpare(op: *Op, t: Page.Kind) Page {
        op.spares -= 1;
        const p = op.reserved.buf[op.spares];
        p.init(t);
        return p;
    }

    /// Frees the spare pages that the operation did not use. The reverse order puts the freelist back as it was.
    fn releaseSpares(self: *BPTree, op: *Op) void {
        while (op.spares > 0) {
            op.spares -= 1;
            self.pageFree(op, op.reserved.buf[op.spares]);
        }
    }

    /// The maximum number of new pages that a chain of splits needs when level `d` gets a cell.
    fn splitPages(path: []const PathEntry, d: usize, splits: bool) usize {
        if (!splits) return 0;
        var n: usize = 1;
        var k = d;
        while (k > 0) {
            k -= 1;
            if (path[k].page.freeBytes() >= max_sep) return n;
            n += 1;
        }
        return n + 1; // a new root
    }

    /// Holds the siblings that `rebalance` can use, from level `d` up.
    /// Returns the maximum number of new pages that its redistributions need.
    fn holdSiblings(self: *BPTree, op: *Op, path: []PathEntry, d: usize) !usize {
        var spares: usize = 0;
        var k = d;
        while (k > 0) : (k -= 1) {
            std.debug.assert(k - 1 >= op.top);
            const parent = path[k - 1].page;
            const idx = path[k - 1].idx;
            const sib = try self.getPage(parent.child(if (idx > 0) idx - 1 else idx + 1));
            self.pool.latch(sib, .exclusive);
            op.held.push(.{ .page = sib, .mode = .exclusive });
            path[k].sib = sib;
            if (sib.kind() != path[k].page.kind()) return error.BadFile;
            spares = @max(spares, splitPages(path, k - 1, parent.freeBytes() < max_sep));
            // A merge or a redistribution at level k removes at most one separator from the parent.
            if (parent.usedBytes() >= min_fill + max_sep) break;
        }
        return spares;
    }

    /// Holds the path from the root to the leaf for `key` until `releaseHeld`.
    fn descend(self: *BPTree, op: *Op, key: []const u8, how: Descent) !Path {
        errdefer self.releaseHeld(op);
        const mode: Latch = if (how == .write) .exclusive else .shared;
        self.lockRoot(op, mode);
        var path: Path = .{};
        var pgno = self.root;
        while (true) {
            const p = try self.getPage(pgno);
            self.pool.latch(p, mode);
            op.held.push(.{ .page = p, .mode = mode });
            const e = &path.entries[path.depth];
            e.* = .{ .page = p, .idx = undefined };
            if (how == .optimistic and p.kind() == .leaf) {
                self.pool.unlatch(p, .shared);
                self.pool.latch(p, .exclusive);
                op.held.buf[op.held.len - 1].mode = .exclusive;
            }
            if (how != .write or p.kind() == .internal and isSafe(p, path.depth == 0))
                self.releaseAbove(op);
            switch (p.kind()) {
                .leaf => return path,
                .internal => {},
                else => return error.BadFile,
            }
            e.idx = p.childIndex(key);
            pgno = p.child(e.idx);
            path.depth += 1;
            if (path.depth >= max_depth) return error.BadFile;
        }
    }

    pub fn get(self: *BPTree, key: []const u8, out: []u8) !?[]u8 {
        if (key.len > max_key) return error.KeyTooLarge;
        var op: Op = .{};
        const path = try self.descend(&op, key, .read);
        defer self.releaseHeld(&op);
        const leaf = path.leaf();
        const r = leaf.search(key);
        if (r.found) {
            const val = leaf.leafVal(r.index);
            if (out.len < val.len) return error.NoSpaceLeft;
            @memcpy(out[0..val.len], val);
            return out[0..val.len];
        }
        return null;
    }

    /// true if split. The caller holds the path and reserves the new pages.
    fn insertUp(self: *BPTree, op: *Op, path: []const PathEntry, d: usize, idx: usize, c: []const u8) bool {
        std.debug.assert(d >= op.top);
        const p = path[d].page;
        if (p.insertCell(idx, c)) {
            self.changed(op, p);
            return false;
        }

        const cl = &op.scratch;
        cl.reset();
        for (0..p.count()) |i| {
            if (i == idx) cl.add(c);
            cl.add(p.cell(i));
        }
        if (idx == p.count()) cl.add(c);

        const leaf = p.kind() == .leaf;
        const s = cl.chooseSplit(leaf);
        const right = takeSpare(op, p.kind());
        const right_pg = right.pgno;
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
        self.changed(op, right);
        self.changed(op, p);

        if (d == 0) {
            std.debug.assert(op.root_latch == .exclusive);
            const root = takeSpare(op, .internal);
            root.setLink(p.pgno);
            _ = root.insertCell(0, sep);
            self.root = root.pgno;
            self.changed(op, root);
        } else {
            _ = self.insertUp(op, path, d - 1, path[d - 1].idx, sep);
        }
        return true;
    }

    fn putIn(self: *BPTree, op: *Op, key: []const u8, val: []const u8, how: Descent) !bool {
        var path = try self.descend(op, key, how);
        defer self.finish(op);
        const leaf = path.leaf();
        defer self.releaseSpares(op);

        const r = leaf.search(key);
        const old_sz = if (r.found) leaf.cell(r.index).len + 2 else 0;
        const new_sz = 4 + key.len + val.len + 2;
        const splits = leaf.freeBytes() + old_sz < new_sz;
        const underflows = r.found and !splits and leaf.usedBytes() - old_sz + new_sz < min_fill;
        if (!splits and !underflows) {
            self.releaseAbove(op);
        } else if (how == .optimistic) {
            return false;
        }
        var spares = splitPages(path.slice(), path.depth, splits);
        if (underflows)
            spares = @max(spares, try self.holdSiblings(op, path.slice(), path.depth));
        try self.reserve(op, spares);

        // Nothing below can fail, so the tree changes completely or not at all.
        if (r.found) {
            leaf.deleteCell(r.index);
            self.changed(op, leaf);
        }
        var c: [4 + max_key + max_val]u8 = undefined;
        const split = self.insertUp(op, path.slice(), path.depth, r.index, makeLeafCell(&c, key, val));
        std.debug.assert(split == splits);
        if (r.found and !split)
            self.rebalance(op, path.slice(), path.depth);
        return true;
    }

    pub fn put(self: *BPTree, key: []const u8, val: []const u8) !void {
        if (key.len > max_key) return error.KeyTooLarge;
        if (val.len > max_val) return error.ValueTooLarge;
        var op: Op = .{};
        if (!try self.putIn(&op, key, val, .optimistic))
            _ = try self.putIn(&op, key, val, .write);
        if (self.durable) try self.pool.wal.flushTo(self.pool.io, op.lsn);
    }

    /// The caller holds the path and the siblings, and reserves the new pages.
    fn rebalance(self: *BPTree, op: *Op, path: []const PathEntry, d: usize) void {
        std.debug.assert(d >= op.top);
        const p = path[d].page;

        if (d == 0) {
            if (p.kind() == .internal and p.count() == 0) {
                std.debug.assert(op.root_latch == .exclusive);
                self.root = p.link();
                self.pageFree(op, p);
            }
            return;
        }

        if (p.usedBytes() >= min_fill) return;

        const parent = path[d - 1].page;
        const idx = path[d - 1].idx;
        const sep_idx = if (idx > 0) idx - 1 else idx;
        const sib = path[d].sib.?;
        const left = if (idx > 0) sib else p;
        const right = if (idx > 0) p else sib;
        std.debug.assert(parent.child(sep_idx) == left.pgno and parent.child(sep_idx + 1) == right.pgno);
        const leaf = left.kind() == .leaf;

        const cl = &op.scratch;
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
            self.pageFree(op, right);
            self.changed(op, left);
            parent.deleteCell(sep_idx);
            self.changed(op, parent);
            self.rebalance(op, path, d - 1);
            return;
        }

        // split evenly
        const s = cl.chooseSplit(leaf);
        var sep_buf: [max_key + 6]u8 = undefined;
        const right_pg = right.pgno;
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
        self.changed(op, left);
        self.changed(op, right);
        parent.deleteCell(sep_idx);
        self.changed(op, parent);

        if (!self.insertUp(op, path, d - 1, sep_idx, sep)) {
            self.rebalance(op, path, d - 1);
        }
    }

    fn deleteIn(self: *BPTree, op: *Op, key: []const u8, how: Descent) !?bool {
        var path = try self.descend(op, key, how);
        defer self.finish(op);
        const leaf = path.leaf();
        defer self.releaseSpares(op);

        const r = leaf.search(key);
        if (!r.found) return false;
        const old_sz = leaf.cell(r.index).len + 2;
        if (leaf.usedBytes() - old_sz < min_fill) {
            if (how == .optimistic) return null;
            try self.reserve(op, try self.holdSiblings(op, path.slice(), path.depth));
        } else {
            self.releaseAbove(op);
        }

        // Nothing below can fail, so the tree changes completely or not at all.
        leaf.deleteCell(r.index);
        self.changed(op, leaf);
        self.rebalance(op, path.slice(), path.depth);
        return true;
    }

    pub fn delete(self: *BPTree, key: []const u8) !bool {
        if (key.len > max_key) return error.KeyTooLarge;
        var op: Op = .{};
        const found = try self.deleteIn(&op, key, .optimistic) orelse (try self.deleteIn(&op, key, .write)).?;
        if (self.durable) try self.pool.wal.flushTo(self.pool.io, op.lsn);
        return found;
    }

    /// Calls `visit` for each key in `lo..hi`. `lo` is inclusive and `hi` is exclusive. A null bound has no limit.
    /// The key and value slices are valid only during the call to `visit`.
    pub fn scan(
        self: *BPTree,
        lo: ?[]const u8,
        hi: ?[]const u8,
        ctx: anytype,
        comptime visit: fn (ctx: @TypeOf(ctx), key: []const u8, val: []const u8) anyerror!void,
    ) !usize {
        var start_buf: [max_key]u8 = undefined;
        var start: []const u8 = lo orelse "";
        var after: bool = false;
        var count: usize = 0;

        restart: while (true) {
            var op: Op = .{};
            const path = try self.descend(&op, start, .read);
            _ = op.held.pop();
            self.releaseHeld(&op);
            var leaf = path.leaf();
            defer self.release(&op, .{ .page = leaf, .mode = .shared });

            const r = leaf.search(start);
            var i = if (after and r.found) r.index + 1 else r.index;

            while (true) {
                const first = i;
                for (i..leaf.count()) |j| {
                    const k = leaf.cellKey(j);
                    if (hi) |h| if (!std.mem.lessThan(u8, k, h)) return count;
                    try visit(ctx, k, leaf.leafVal(j));
                    count += 1;
                }
                const next = leaf.link();
                if (next == 0) return count;
                const p = try self.getPage(next);
                if (!self.pool.tryLatch(p, .shared)) {
                    self.pool.unpin(p, .clean);
                    if (leaf.count() > first) {
                        const k = leaf.cellKey(leaf.count() - 1);
                        @memcpy(start_buf[0..k.len], k);
                        start = start_buf[0..k.len];
                        after = true;
                    }
                    continue :restart;
                }
                self.release(&op, .{ .page = leaf, .mode = .shared });
                leaf = p;
                if (leaf.kind() != .leaf) return error.BadFile;
                i = 0;
            }
        }
    }

    pub fn check(self: *BPTree, gpa: Allocator) !void {
        const seen = try gpa.alloc(bool, self.npages);
        defer gpa.free(seen);
        @memset(seen, false);
        var st: CheckState = .{ .seen = seen };
        try self.checkPage(&st, self.root, 0, null, null);
        if (st.next_leaf != 0) return checkFail("the last page links to {d}", .{st.next_leaf.?});

        var pg = self.freelist;
        while (pg != 0) {
            if (pg >= self.npages or seen[pg]) return checkFail("free list: page {d} is out of range or seen twice", .{pg});
            seen[pg] = true;
            const p = try self.getPage(pg);
            defer self.pool.unpin(p, .clean);
            if (p.kind() != .free) return checkFail("page {d} is on the free list but not free", .{pg});
            pg = p.link();
        }
        for (seen[1..], 1..) |s, i| {
            if (!s) return checkFail("page {d} is neither in the tree nor on the free list", .{i});
        }
        if (self.pool.pinned() != 0) return checkFail("{d} pins left over", .{self.pool.pinned()});
    }

    const CheckState = struct {
        seen: []bool,
        leaf_depth: ?usize = null,
        next_leaf: ?u32 = null,
    };

    fn checkPage(self: *BPTree, st: *CheckState, pgno: u32, depth: usize, lo: ?[]const u8, hi: ?[]const u8) !void {
        if (pgno == meta_pgno or pgno >= self.npages or st.seen[pgno])
            return checkFail("page {d} is out of range or seen twice", .{pgno});
        st.seen[pgno] = true;
        const p = try self.getPage(pgno);
        defer self.pool.unpin(p, .clean);

        const n = p.count();
        if (pgno != self.root and p.usedBytes() < min_fill) return checkFail("page {d} is below min_fill", .{pgno});
        for (0..n) |i| {
            const k = p.cellKey(i);
            if (i > 0 and !std.mem.lessThan(u8, p.cellKey(i - 1), k))
                return checkFail("page {d}: keys out of order", .{pgno});
            if (lo != null and std.mem.lessThan(u8, k, lo.?) or hi != null and !std.mem.lessThan(u8, k, hi.?))
                return checkFail("page {d}: key outside its parent's range", .{pgno});
        }
        switch (p.kind()) {
            .leaf => {
                if (st.leaf_depth == null) st.leaf_depth = depth;
                if (st.leaf_depth != depth) return checkFail("leaf {d} is at depth {d}, not {d}", .{ pgno, depth, st.leaf_depth.? });
                if (st.next_leaf != null and st.next_leaf != pgno)
                    return checkFail("the leaf before {d} links to {d}", .{ pgno, st.next_leaf.? });
                st.next_leaf = p.link();
            },
            .internal => {
                if (n == 0)
                    return checkFail("internal page {d} has no keys", .{pgno});
                for (0..n + 1) |i| {
                    const clo = if (i == 0) lo else p.cellKey(i - 1);
                    const chi = if (i == n) hi else p.cellKey(i);
                    try self.checkPage(st, p.child(i), depth + 1, clo, chi);
                }
            },
            else => return checkFail("page {d} has type {d}", .{ pgno, @backingInt(p.kind()) }),
        }
    }
};

fn checkFail(comptime fmt: []const u8, args: anytype) error{CheckFailed} {
    std.log.err("check: " ++ fmt, args);
    return error.CheckFailed;
}

fn isSafe(p: Page, is_root: bool) bool {
    if (p.freeBytes() < max_sep) return false;
    return if (is_root) p.count() >= 2 else p.usedBytes() >= min_fill + max_sep;
}

const Page = struct {
    page: *[page_size]u8,
    pgno: u32 = 0,

    /// Non-exhaustive, because a corrupt file can contain any byte.
    const Kind = enum(u8) {
        free = 0,
        leaf = 1,
        internal = 2,
        _,
    };

    fn init(self: Page, t: Kind) void {
        @memset(self.page, 0);
        self.page[0] = @backingInt(t);
        self.setCellStart(page_size);
    }

    fn kind(self: Page) Kind {
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

    fn fill(self: Page, t: Kind, link_pgno: u32, cl: *const CellList, from: usize, to: usize) void {
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

fn createTestLog(dir: Io.Dir) !Io.File {
    return dir.createFile(std.testing.io, "test.bin.wal", .{ .read = true });
}

test BPTree {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);

    try t.metaWrite(5);
    try t.metaRead();
    try std.testing.expectEqual(5, t.pool.wal.epoch);
    // The newer of the two copies wins, and a torn copy is ignored.
    try t.metaWrite(6);
    try t.metaRead();
    try std.testing.expectEqual(6, t.pool.wal.epoch);
    try file.writePositionalAll(std.testing.io, "x", 3);
    try t.metaRead();
    try std.testing.expectEqual(5, t.pool.wal.epoch);
}

test "BPTree sync and reopen" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var kbuf: [16]u8 = undefined;
    var out: [max_val]u8 = undefined;
    const N = 500;
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    {
        var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
        defer t.deinit(std.testing.allocator);
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        try t.sync();
    }
    // A new tree has an empty pool, so it reads all pages from the file.
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);
    for (0..N) |i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        try std.testing.expectEqualStrings("value", (try t.get(k, &out)).?);
    }
}

test "BPTree recovers after a crash" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer log.close(io);

    var kbuf: [16]u8 = undefined;
    var out: [max_val]u8 = undefined;
    const N = 2000;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit(std.testing.allocator);
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        for (0..N) |i| {
            if (i % 3 == 0) _ = try t.delete(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}));
        }
        // No sync: deinit drops the pool, as a crash would. Some pages reached the file and some did not.
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit(std.testing.allocator);
    try t.check(std.testing.allocator);
    for (0..N) |i| {
        const got = try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out);
        if (i % 3 == 0) try std.testing.expectEqual(null, got) else try std.testing.expectEqualStrings("value", got.?);
    }
}

test "BPTree recovery ignores an operation that did not commit" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer log.close(io);

    var kbuf: [16]u8 = undefined;
    var out: [max_val]u8 = undefined;
    const N = 500;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit(std.testing.allocator);
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        // An operation that crashed after it logged an image of the root, but before its commit record.
        var junk: [page_size]u8 = @splat(0xEE);
        const end = try t.pool.wal.append(io, &.{.{ .page = &junk }}, 0);
        try log.setLength(io, end - Wal.rec_hdr);
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit(std.testing.allocator);
    try t.check(std.testing.allocator);
    for (0..N) |i| try std.testing.expectEqualStrings("value", (try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out)).?);
}

test "BPTree bad file" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    try file.writePositionalAll(io, "garbage!", 0);
    try std.testing.expectError(error.BadFile, BPTree.init(std.testing.allocator, io, file, log));
}

test Wal {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const log = try createTestLog(tmp.dir);
    defer log.close(io);
    var w: Wal = .{ .file = log, .epoch = 7 };

    var a: [page_size]u8 = @splat('a');
    var b: [page_size]u8 = @splat('b');
    const pa: Page = .{ .page = &a, .pgno = 3 };
    const pb: Page = .{ .page = &b, .pgno = 4 };
    const pc: Page = .{ .page = &a, .pgno = 5 };
    const first = try w.append(io, &.{ pa, pb }, 0);
    const second = try w.append(io, &.{pc}, 9);
    try std.testing.expectEqual(3 * Wal.rec_hdr + 2 * page_size, first);
    try std.testing.expectEqual(second, w.end.raw);

    // Read it all back: page 3, page 4, commit, page 5, commit with root 9, and then the end.
    var buf: [page_size]u8 = undefined;
    var off: u64 = 0;
    const want = [_]struct { Wal.Kind, u32, u8 }{ .{ .page, 3, 'a' }, .{ .page, 4, 'b' }, .{ .commit, 0, 0 }, .{ .page, 5, 'a' }, .{ .commit, 9, 0 } };
    for (want) |wnt| {
        const r = (try w.next(io, off, &buf)).?;
        try std.testing.expectEqual(wnt[0], r.kind);
        try std.testing.expectEqual(wnt[1], r.arg);
        if (r.kind == .page) try std.testing.expectEqual(wnt[2], buf[100]);
        off = r.end;
    }
    try std.testing.expectEqual(second, off);
    try std.testing.expectEqual(null, try w.next(io, off, &buf));

    // A torn record ends the log there.
    try log.writePositionalAll(io, "x", first + Wal.rec_hdr + 100);
    try std.testing.expectEqual(null, try w.next(io, first, &buf));
    try std.testing.expect(try w.next(io, 0, &buf) != null);

    // So does a record from another epoch.
    w.epoch = 8;
    try std.testing.expectEqual(null, try w.next(io, 0, &buf));
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
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);

    t.npages = pool_frames + 4;
    for (1..t.npages) |pg| {
        const p = try t.pool.pin(@intCast(pg), .no_load);
        p.init(.leaf);
        try std.testing.expectEqual(pg, p.pgno);
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
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);

    // open allocates the root leaf as page 1.
    try std.testing.expectEqual(1, t.root);
    try std.testing.expectEqual(2, t.npages);

    const a = try t.pageAlloc(.leaf);
    const a_pgno = a.pgno;
    try std.testing.expectEqual(2, a_pgno);
    try std.testing.expectEqual(.leaf, a.kind());
    try std.testing.expectEqual(3, t.npages);

    var op: Op = .{};
    op.reserved.push(a);
    t.pageFree(&op, a);
    try std.testing.expectEqual(0, t.freelist);
    t.finish(&op);
    try std.testing.expectEqual(a_pgno, t.freelist);
    try std.testing.expectEqual(0, t.pool.pinned());

    const b = try t.pageAlloc(.internal);
    try std.testing.expectEqual(a_pgno, b.pgno);
    try std.testing.expectEqual(.internal, b.kind());
    try std.testing.expectEqual(0, t.freelist);
    try std.testing.expectEqual(3, t.npages);
    t.pool.unpin(b, .dirty);
    try std.testing.expectEqual(0, t.pool.pinned());
}

/// A pin of page `pgno` and its unpin, with no I/O.
fn testPin(pool: *Pool, pgno: u32) !void {
    pool.unpin(try pool.pin(pgno, .no_load), .clean);
}

/// Empties the pool of a new tree.
fn testEmptyPool(t: *BPTree) void {
    // init synced the tree, so no frame is dirty and the pages can go.
    t.pool.frames = @splat(.{});
    for (&t.pool.table) |*part| part.map.clearRetainingCapacity();
    t.pool.hand.store(0, .monotonic);
}

/// Sets the usage count of a frame that no other thread uses.
fn testSetUsage(fr: *Frame, usage: u4) void {
    var s = fr.load();
    s.usage = usage;
    fr.state.store(@bitCast(s), .monotonic);
}

test "Pool usage count" {
    if (build_options.pool_paranoid) return error.SkipZigTest;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);
    testEmptyPool(&t);

    // A miss gives a usage count of 1, and each pin of the page in the pool adds 1, up to max_usage.
    try testPin(&t.pool, 1);
    const fr = &t.pool.frames[t.pool.find(1).?];
    try std.testing.expectEqual(1, fr.load().usage);
    for (0..max_usage + 3) |i| {
        try testPin(&t.pool, 1);
        try std.testing.expectEqual(@min(i + 2, max_usage), fr.load().usage);
    }

    // Two owners pin the page at the same time: each pin counts. An unpin does not change the count.
    testSetUsage(fr, 0);
    const a = try t.pool.pin(1, .no_load);
    const b = try t.pool.pin(1, .no_load);
    try std.testing.expectEqual(@min(2, max_usage), fr.load().usage);
    t.pool.unpin(a, .clean);
    t.pool.unpin(b, .clean);
    try std.testing.expectEqual(@min(2, max_usage), fr.load().usage);
    try std.testing.expectEqual(0, t.pool.pinned());
}

test "Pool clock sweep" {
    // The test gives page 1 a usage count of 3.
    if (build_options.pool_paranoid or max_usage < 3) return error.SkipZigTest;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);
    testEmptyPool(&t);

    // An empty frame has no pins and a usage count of 0, so the sweep takes the empty frames in order.
    // Pages 1 to pool_frames fill them, each with a usage count of 1, and the hand goes round once.
    // Two more pins give page 1 a usage count of 3.
    for (1..pool_frames + 1) |pg| try testPin(&t.pool, @intCast(pg));
    for (0..pool_frames) |f| try std.testing.expectEqual(f + 1, t.pool.frames[f].pgno.?);
    try testPin(&t.pool, 1);
    try testPin(&t.pool, 1);
    try std.testing.expectEqual(3, t.pool.frames[0].load().usage);
    try std.testing.expectEqual(0, t.pool.hand.raw % pool_frames);

    // The first pass takes page 1 to 2 and the others to 0. The second pass takes page 1 to 1,
    // and page 2 (frame 1) is the victim.
    const moves = t.pool.hand.raw;
    try testPin(&t.pool, pool_frames + 1);
    try std.testing.expectEqual(pool_frames + 2, t.pool.hand.raw - moves);
    try std.testing.expectEqual(2, t.pool.hand.raw % pool_frames);
    try std.testing.expectEqual(pool_frames + 1, t.pool.frames[1].pgno.?);
    try std.testing.expectEqual(1, t.pool.frames[0].load().usage);
    try std.testing.expectEqual(1, t.pool.frames[1].load().usage);
    for (2..pool_frames) |f| try std.testing.expectEqual(0, t.pool.frames[f].load().usage);

    // The next miss takes the frame under the hand at once: page 3, with a usage count of 0.
    try testPin(&t.pool, pool_frames + 2);
    try std.testing.expectEqual(pool_frames + 2, t.pool.frames[2].pgno.?);
    try std.testing.expectEqual(null, t.pool.find(3));
}

test "Pool clock sweep skips pinned frames" {
    if (build_options.pool_paranoid) return error.SkipZigTest;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);
    testEmptyPool(&t);

    var pinned: [pool_frames]Page = undefined;
    for (&pinned, 1..) |*p, pg| p.* = try t.pool.pin(@intCast(pg), .no_load);
    // Every frame has a pin. One pass with no change to a usage count gives up.
    const moves = t.pool.hand.raw;
    try std.testing.expectError(error.PoolExhausted, t.pool.pin(pool_frames + 1, .no_load));
    try std.testing.expectEqual(pool_frames, t.pool.hand.raw - moves);

    // With one frame free of pins, the sweep finds it, however many pinned frames it passes.
    const last = pool_frames - 1;
    t.pool.unpin(pinned[last], .clean);
    const p = try t.pool.pin(pool_frames + 1, .no_load);
    try std.testing.expectEqual(last, t.pool.frameIndex(p));
    t.pool.unpin(p, .clean);
    for (pinned[0..last]) |q| t.pool.unpin(q, .clean);
    try std.testing.expectEqual(0, t.pool.pinned());
}

test "Pool miss gives up a victim that another thread pinned" {
    if (build_options.pool_paranoid) return error.SkipZigTest;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);
    testEmptyPool(&t);
    const pool = &t.pool;

    // Page 1 is in frame 0 with a usage count of 0. With the hand back on frame 0, the sweep takes it and pins it.
    try testPin(pool, 1);
    const f = pool.find(1).?;
    testSetUsage(&pool.frames[f], 0);
    pool.hand.store(f, .monotonic);
    try std.testing.expectEqual(f, try pool.sweep());

    // Before the miss changes the page table, another thread finds page 1 in it and pins it.
    const p = try pool.pin(1, .no_load);
    // The miss sees the second pin: it neither writes the page nor takes it out of the page table.
    const writes = pool.writes.raw;
    try std.testing.expect(!try pool.writeVictim(f));
    try std.testing.expect(!pool.unmap(f));
    try std.testing.expectEqual(writes, pool.writes.raw);
    try std.testing.expectEqual(1, pool.frames[f].pgno.?);

    // The miss gives the frame back. The page stays in its frame for the other thread.
    _ = Pool.unpinFrame(&pool.frames[f], false);
    try std.testing.expectEqual(1, pool.pinned());
    try std.testing.expectEqual(f, pool.find(1).?);
    pool.unpin(p, .clean);
}

test "BPTree get" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);

    // Make a two-level tree by hand: the root holds "m", with "a" on the left and "m", "z" on the right.
    var cell: [page_size]u8 = undefined;
    const left = try t.getPage(t.root);
    try std.testing.expect(left.insertCell(0, makeLeafCell(&cell, "a", "1")));

    const right = try t.pageAlloc(.leaf);
    try std.testing.expect(right.insertCell(0, makeLeafCell(&cell, "m", "2")));
    try std.testing.expect(right.insertCell(1, makeLeafCell(&cell, "z", "3")));

    const root = try t.pageAlloc(.internal);
    root.setLink(left.pgno);
    try std.testing.expect(root.insertCell(0, makeInternalCell(&cell, right.pgno, "m")));
    t.root = root.pgno;
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

    var op: Op = .{};
    const path = try t.descend(&op, "z", .write);
    defer t.releaseHeld(&op);
    try std.testing.expectEqual(1, path.depth);
    try std.testing.expectEqual(t.root, path.entries[0].page.pgno);
    try std.testing.expectEqual(1, path.entries[0].idx);
    try std.testing.expectEqual(right.pgno, path.entries[1].page.pgno);
    try std.testing.expectEqual(right.pgno, path.leaf().pgno);
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
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
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
    try t.check(std.testing.allocator);

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
    try t.check(std.testing.allocator);

    const root = try t.getPage(t.root);
    defer t.pool.unpin(root, .clean);
    try std.testing.expectEqual(.leaf, root.kind());
    try std.testing.expectEqual(0, root.count());
}

test "BPTree scan" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);

    // Only the odd numbers, so that a bound can fall between two keys.
    const N = 2000;
    var kbuf: [16]u8 = undefined;
    var vbuf: [16]u8 = undefined;
    for (0..N) |i| {
        if (i % 2 == 0) continue;
        try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), try std.fmt.bufPrint(&vbuf, "v{d}", .{i}));
    }
    try std.testing.expect(t.npages > 3);

    const Check = struct {
        next: usize,
        fn visit(self: *@This(), key: []const u8, val: []const u8) !void {
            var kb: [16]u8 = undefined;
            var vb: [16]u8 = undefined;
            try std.testing.expectEqualStrings(try std.fmt.bufPrint(&kb, "key{d:0>8}", .{self.next}), key);
            try std.testing.expectEqualStrings(try std.fmt.bufPrint(&vb, "v{d}", .{self.next}), val);
            self.next += 2;
        }
    };

    var c: Check = .{ .next = 1 };
    try std.testing.expectEqual(N / 2, try t.scan(null, null, &c, Check.visit));
    try std.testing.expectEqual(0, t.pool.pinned());

    // The lower bound is inclusive and the upper bound is exclusive. A bound between two keys starts or stops at the nearest key inside it.
    c = .{ .next = 101 };
    try std.testing.expectEqual(700, try t.scan("key00000101", "key00001501", &c, Check.visit));
    try std.testing.expectEqual(1501, c.next);
    try std.testing.expectEqual(0, t.pool.pinned());

    c = .{ .next = 101 };
    try std.testing.expectEqual(699, try t.scan("key00000101", "key00001499", &c, Check.visit));
    try std.testing.expectEqual(1499, c.next);
    try std.testing.expectEqual(0, t.pool.pinned());

    c = .{ .next = 101 };
    try std.testing.expectEqual(700, try t.scan("key00000100", "key00001500", &c, Check.visit));
    try std.testing.expectEqual(0, t.pool.pinned());

    c = .{ .next = 1001 };
    try std.testing.expectEqual(500, try t.scan("key00001000", null, &c, Check.visit));
    try std.testing.expectEqual(0, t.pool.pinned());

    c = .{ .next = 1 };
    try std.testing.expectEqual(0, try t.scan("key00000002", "key00000002", &c, Check.visit));
    try std.testing.expectEqual(0, t.pool.pinned());

    // Equal bounds give no keys, also when the bound is a key in the tree.
    c = .{ .next = 1 };
    try std.testing.expectEqual(0, try t.scan("key00000003", "key00000003", &c, Check.visit));
    try std.testing.expectEqual(0, t.pool.pinned());

    // An error from visit stops the scan and releases all pins.
    const Stop = struct {
        n: usize = 0,
        fn visit(self: *@This(), _: []const u8, _: []const u8) !void {
            self.n += 1;
            if (self.n == 600) return error.Stop;
        }
    };
    var s: Stop = .{};
    try std.testing.expectError(error.Stop, t.scan(null, null, &s, Stop.visit));
    try std.testing.expectEqual(0, t.pool.pinned());
}

test "BPTree failed operation does not change the tree" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
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
            // Walk the path by hand. descend releases the safe pages above the leaf, so it cannot give their children.
            var skip: Stack(u32, 2 * max_depth) = .{};
            var levels: usize = 0;
            var pg = tree.root;
            while (true) : (levels += 1) {
                const p = try tree.getPage(pg);
                defer tree.pool.unpin(p, .clean);
                skip.push(pg);
                if (p.kind() == .leaf) break;
                const idx = p.childIndex(key);
                skip.push(p.child(if (idx > 0) idx - 1 else idx + 1));
                pg = p.child(idx);
            }
            var count: usize = 0;
            pg = 1;
            while (count < pool_frames - (levels + 1)) : (pg += 1) {
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

test "BPTree pool lock count" {
    if (build_options.pool_paranoid) return error.SkipZigTest;

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer log.close(std.testing.io);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit(std.testing.allocator);
    t.durable = false;

    var kbuf: [16]u8 = undefined;
    var out: [max_val]u8 = undefined;
    const val: [8]u8 = @splat('v');
    // The even keys are in the tree. Most puts of an odd key do not split.
    for (0..2000) |k| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{2 * k}), &val);

    var op: Op = .{};
    const levels = (try t.descend(&op, "key", .read)).depth + 1;
    t.releaseHeld(&op);

    // The fewest locks over 100 keys, so that a rare split or rebalance does not count.
    const kinds = [_][]const u8{ "get", "put new", "put old", "delete" };
    var fewest: [kinds.len]u64 = @splat(std.math.maxInt(u64));
    for (0..100) |i| {
        for (kinds, &fewest) |kind, *f| {
            const odd = std.mem.eql(u8, kind, "put new");
            const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{20 * i + @intFromBool(odd)});
            const before = t.pool.locks.raw;
            if (std.mem.eql(u8, kind, "get")) {
                _ = try t.get(k, &out);
            } else if (std.mem.eql(u8, kind, "delete")) {
                _ = try t.delete(k);
            } else {
                try t.put(k, &val);
            }
            f.* = @min(f.*, t.pool.locks.raw - before);
        }
    }
    // Each pin of a page in the pool locks its partition one time. An unpin does not lock.
    for (fewest) |f| try std.testing.expectEqual(levels, f);
}
