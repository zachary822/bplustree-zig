const std = @import("std");
const build_options = @import("build_options");
const Io = std.Io;
const Allocator = std.mem.Allocator;

const page_size = build_options.page_size;
const pool_frames = build_options.pool_frames;
const max_usage = build_options.max_usage;
const ring_frames: usize = @min(256 * 1024 / page_size, pool_frames / 8);

/// The maximum length of a key.
pub const max_key = page_size / 16;
/// The maximum length of a value. A buffer of this size can hold all values that `get` returns.
pub const max_val = std.math.maxInt(u32);
pub const max_local = page_size / 8;
const max_depth = 32;

const hdr_size = 12;
const capacity = page_size - hdr_size;
const min_fill = capacity / 4;
/// The largest separator cell, with its slot, that a split sends to a parent.
const max_sep = max_key + 6 + 2;
/// fewest bytes of value that leaf cell keeps when there are overflow pages
const min_local = page_size / 16;
const ovfl_cap = page_size - hdr_size;
const max_leaf_cell = 6 + max_key + max_local + 4;

comptime {
    std.debug.assert(page_size >= 256 and page_size <= 32768);
}

const meta_pgno = 0;
const magic = "BPTOVF01";
const meta_size = 32;

/// The errors that the tree gives, in addition to the I/O errors.
pub const Error = error{ BadFile, KeyTooLarge, ValueTooLarge, PoolExhausted, NoSpaceLeft };

fn get16(p: []const u8) u16 {
    return std.mem.readInt(u16, p[0..2], .little);
}

fn get32(p: []const u8) u32 {
    return std.mem.readInt(u32, p[0..4], .little);
}

fn put16(p: []u8, v: u16) void {
    std.mem.writeInt(u16, p[0..2], v, .little);
}

fn put32(p: []u8, v: u32) void {
    std.mem.writeInt(u32, p[0..4], v, .little);
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
    files: [2]Io.File,
    mu: Io.Mutex = .init,
    durable: std.atomic.Value(u64) = .init(0),
    sync_mu: Io.Mutex = .init,
    syncing: bool = false,
    synced: Io.Condition = .init,
    syncs: std.atomic.Value(u64) = .init(0),
    /// The run that `append` writes.
    epoch: u32 = 0,
    /// The LSN of the first record of the run. The record at LSN `lsn` is at offset `lsn - start` of the file.
    start: std.atomic.Value(u64) = .init(0),
    /// The LSN after the last record. An LSN counts the bytes of the log that this process wrote.
    end: std.atomic.Value(u64) = .init(0),

    const rec_hdr = 16;

    const Kind = enum(u8) {
        page = 1,
        commit = 2,
        next = 3,
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

    fn file(self: *Wal) Io.File {
        return self.files[self.epoch % 2];
    }

    fn append(self: *Wal, io: Io, pages: []const Page, root: u32) !u64 {
        self.mu.lockUncancelable(io);
        defer self.mu.unlock(io);
        var off = self.end.raw - self.start.raw;
        var rec: [rec_hdr + page_size]u8 = undefined;
        for (pages) |p| {
            header(rec[0..rec_hdr], self.epoch, .page, p.pgno);
            @memcpy(rec[rec_hdr..], p.page);
            put32(&rec, crc(&rec));
            try self.file().writePositionalAll(io, &rec, off);
            off += rec.len;
        }
        header(rec[0..rec_hdr], self.epoch, .commit, root);
        put32(&rec, crc(rec[0..rec_hdr]));
        try self.file().writePositionalAll(io, rec[0..rec_hdr], off);
        off += rec_hdr;
        self.end.store(self.start.raw + off, .release);
        return self.start.raw + off;
    }

    fn nextRun(self: *Wal, io: Io) !u64 {
        self.mu.lockUncancelable(io);
        defer self.mu.unlock(io);
        var rec: [rec_hdr]u8 = undefined;
        header(&rec, self.epoch, .next, self.epoch + 1);
        put32(&rec, crc(&rec));
        try self.file().writePositionalAll(io, &rec, self.end.raw - self.start.raw);
        const lsn = self.end.raw + rec_hdr;
        self.epoch += 1;
        self.start.store(lsn, .release);
        self.end.store(lsn, .release);
        return lsn;
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
            self.mu.lockUncancelable(io);
            const end = self.end.raw;
            const start = self.start.raw;
            const cur = self.file();
            const prev = self.files[(self.epoch + 1) % 2];
            self.mu.unlock(io);
            self.sync_mu.unlock(io);
            const result = if (self.durable.load(.acquire) < start) prev.sync(io) else {};
            const result2 = if (result) |_| cur.sync(io) else |err| err;
            self.sync_mu.lockUncancelable(io);
            self.syncing = false;
            self.synced.broadcast(io);
            try result2;
            _ = self.syncs.fetchAdd(1, .monotonic);
            self.durable.store(end, .release);
        }
    }

    fn read(self: *Wal, io: Io, epoch: u32, off: u64, buf: *[page_size]u8) !?Record {
        var rec: [rec_hdr + page_size]u8 = undefined;
        const f = self.files[epoch % 2];
        if (try f.readPositionalAll(io, rec[0..rec_hdr], off) < rec_hdr) return null;
        if (get32(rec[4..]) != epoch) return null;
        const kind: Kind = @fromBackingInt(rec[8]);
        const len: usize = switch (kind) {
            .page => rec_hdr + page_size,
            .commit, .next => rec_hdr,
            _ => return null,
        };
        if (len > rec_hdr and try f.readPositionalAll(io, rec[rec_hdr..len], off + rec_hdr) < len - rec_hdr)
            return null;
        if (get32(&rec) != crc(rec[0..len])) return null;
        if (kind == .page) @memcpy(buf, rec[rec_hdr..]);
        return .{ .kind = kind, .arg = get32(rec[12..]), .end = off + len };
    }
};

const LogPos = struct {
    epoch: u32,
    off: u64 = 0,

    fn next(self: *LogPos, wal: *Wal, io: Io, buf: *[page_size]u8) !?Wal.Record {
        const r = (try wal.read(io, self.epoch, self.off, buf)) orelse return null;
        self.off = r.end;
        if (r.kind == .next) {
            if (r.arg != self.epoch + 1) return null;
            self.* = .{ .epoch = r.arg };
        }
        return r;
    }
};

const Ring = struct {
    slots: [@max(ring_frames, 1)]?usize = @splat(null),
    current: usize = 0,
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

    fn pinFound(fr: *Frame, ring: bool) void {
        var s = fr.load();
        while (true) {
            var n = s;
            n.pins += 1;
            if (ring) {
                n.usage = @max(n.usage, 1);
            } else if (n.usage < max_usage) {
                n.usage += 1;
            }
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

    fn fromRing(self: *Pool, ring: *Ring) ?usize {
        ring.current = (ring.current + 1) % ring.slots.len;
        const f = ring.slots[ring.current] orelse return null;
        const fr = &self.frames[f];
        var s = fr.load();
        while (s.pins == 0 and s.usage <= 1) {
            var n = s;
            n.pins = 1;
            s = fr.cas(s, n) orelse return f;
        }
        return null;
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

    fn victim(self: *Pool, ring: ?*Ring) !usize {
        while (true) {
            var from_ring = false;
            const f = blk: {
                if (ring) |r| if (self.fromRing(r)) |f| {
                    from_ring = true;
                    break :blk f;
                };
                const f = try self.sweep();
                if (ring) |r| r.slots[r.current] = f;
                break :blk f;
            };
            const fr = &self.frames[f];
            const s = fr.load();
            if (s.dirty) {
                if (from_ring and fr.lsn.load(.acquire) > self.wal.durable.load(.acquire)) {
                    ring.?.slots[ring.?.current] = null;
                    _ = unpinFrame(fr, false);
                    continue;
                }
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

    fn pin(self: *Pool, page: u32, mode: Load) !Page {
        return self.pinWith(page, mode, null);
    }

    fn pinWith(self: *Pool, pgno: u32, mode: Load, ring: ?*Ring) !Page {
        std.debug.assert(pgno != meta_pgno);
        _ = self.lookups.fetchAdd(1, .monotonic);
        const part = self.partition(pgno);
        self.lockPart(part, .shared);
        if (part.map.get(pgno)) |f| {
            pinFound(&self.frames[f], ring != null);
            part.lock.unlockShared(self.io);
            return self.ready(f);
        }
        part.lock.unlockShared(self.io);

        const v = try self.victim(ring);
        const fr = &self.frames[v];
        self.lockPart(part, .exclusive);
        const entry = part.map.getOrPutAssumeCapacity(pgno);
        if (entry.found_existing) {
            // another thread put the page in a frame while this one looked for a victim. the victim stays empty.
            _ = unpinFrame(fr, false);
            const f = entry.value_ptr.*;
            pinFound(&self.frames[f], ring != null);
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
    old_chain: u32 = 0,

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

    fn pageFree(op: *Op, p: Page) void {
        std.debug.assert(op.owns(p));
        p.init(.free);
        op.freed.push(p);
    }

    fn markChanged(op: *Op, p: Page) void {
        std.debug.assert(op.owns(p));
        for (op.changed.items()) |c| if (c.page == p.page) return;
        op.changed.push(p);
    }

    /// Frees the spare pages that the operation did not use. The reverse order puts the freelist back as it was.
    fn releaseSpares(op: *Op) void {
        while (op.spares > 0) {
            op.spares -= 1;
            op.pageFree(op.reserved.buf[op.spares]);
        }
    }
};

pub const BPTree = struct {
    pool: Pool,
    gpa: Allocator,
    root: u32 = 0,
    npages: u32 = 0,
    freelist: u32 = 0,

    root_latch: Io.RwLock = .init,
    alloc_mu: Io.Mutex = .init,
    gate: Io.RwLock = .init,
    durable: bool = true,
    pending: ?Checkpoint = null,

    const Checkpoint = struct {
        epoch: u32,
        root: u32,
        npages: u32,
        freelist: u32,
    };

    /// Opens the tree in `file`, which must be open for read and write. If the file is empty, it makes an empty tree.
    /// The caller owns `file` and must keep it open until `deinit`.
    pub fn init(gpa: Allocator, io: Io, file: Io.File, logs: [2]Io.File) !BPTree {
        const mem = try gpa.alloc(u8, page_size * pool_frames);
        errdefer gpa.free(mem);
        var t: BPTree = .{
            .pool = .{ .io = io, .file = file, .wal = .{ .files = logs }, .mem = mem },
            .gpa = gpa,
        };
        try t.pool.initTable(gpa);
        errdefer t.pool.deinitTable(gpa);

        if (try file.length(io) == 0) {
            for (logs) |log| {
                try log.setLength(io, 0);
                try log.sync(io);
            }
            t.npages = 1;
            const root = try t.pageAlloc(.leaf);
            t.root = root.pgno;
            t.pool.unpin(root, .dirty);
            try t.sync();
        } else {
            try t.metaRead();
            try t.recover();
        }

        return t;
    }

    /// Releases the memory. It does not close the file. Changes that `sync` did not write are lost.
    pub fn deinit(self: *BPTree) void {
        self.pool.deinit(self.gpa);
    }

    pub fn sync(self: *BPTree) !void {
        self.gate.lockUncancelable(self.pool.io);
        defer self.gate.unlock(self.pool.io);
        try self.syncLocked();
    }

    /// Writes all changed pages and the meta page, and then syncs the file.
    fn syncLocked(self: *BPTree) !void {
        const io = self.pool.io;
        const ck = self.pending orelse blk: {
            _ = try self.pool.wal.nextRun(io);
            break :blk self.here();
        };
        self.pending = ck;
        try self.pool.wal.flushTo(io, self.pool.wal.end.load(.acquire));
        try self.pool.flush();
        try self.checkpointEnd(ck);
        self.pending = null;
    }

    fn here(self: *BPTree) Checkpoint {
        return .{ .epoch = self.pool.wal.epoch, .root = self.root, .npages = self.npages, .freelist = self.freelist };
    }

    fn checkpointEnd(self: *BPTree, ck: Checkpoint) !void {
        const io = self.pool.io;
        try self.pool.file.sync(io);
        try self.metaWrite(ck);
        try self.pool.file.sync(io);
        try self.pool.wal.files[(ck.epoch + 1) % 2].setLength(io, 0);
    }

    fn metaWrite(self: *BPTree, ck: Checkpoint) !void {
        var buf: [meta_size]u8 = undefined;
        @memcpy(buf[0..magic.len], magic);
        put32(buf[8..], @intCast(page_size));
        put32(buf[12..], ck.epoch);
        put32(buf[16..], ck.root);
        put32(buf[20..], ck.npages);
        put32(buf[24..], ck.freelist);
        put32(buf[28..], std.hash.Crc32.hash(buf[0..28]));
        try self.pool.file.writePositionalAll(self.pool.io, &buf, ck.epoch % 2 * (page_size / 2));
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

    fn recover(self: *BPTree) !void {
        const io = self.pool.io;
        const wal = &self.pool.wal;
        var buf: [page_size]u8 = undefined;

        const first = wal.epoch;

        var pos: LogPos = .{ .epoch = first };
        var n: usize = 0;
        var committed: usize = 0;
        var root = self.root;
        while (try pos.next(wal, io, &buf)) |r| {
            n += 1;
            if (r.kind != .commit) continue;
            committed = n;
            if (r.arg != 0) root = r.arg;
        }

        pos = .{ .epoch = first };
        for (0..committed) |_| {
            const r = (try pos.next(wal, io, &buf)).?;
            if (r.kind != .page) continue;
            if (r.arg == meta_pgno) return error.BadFile;
            try self.pool.write(r.arg, &buf);
            self.npages = @max(self.npages, r.arg + 1);
        }
        self.root = root;
        if (n > 0) try self.rebuildFreeList();

        wal.epoch = first + 3;
        try self.pool.flush();
        try self.checkpointEnd(self.here());
        try wal.file().setLength(io, 0);
    }

    fn rebuildFreeList(self: *BPTree) !void {
        const seen = try self.gpa.alloc(bool, self.npages);
        defer self.gpa.free(seen);
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
            .leaf => for (0..p.count()) |i| try self.markChain(seen, p.overflow(i)),
            .internal => for (0..p.count() + 1) |i| try self.markReachable(seen, p.child(i), depth + 1),
            else => return error.BadFile,
        }
    }

    fn markChain(self: *BPTree, seen: []bool, first: u32) !void {
        var pg = first;
        while (pg != 0) {
            if (pg == meta_pgno or pg >= self.npages or seen[pg]) return error.BadFile;
            seen[pg] = true;
            const p = try self.getPage(pg);
            defer self.pool.unpin(p, .clean);
            if (p.kind() != .overflow) return error.BadFile;
            pg = p.link();
        }
    }

    pub const VacuumMode = union(enum) {
        truncate,
        full,
        incremental: u32,
    };

    pub const VacuumStats = struct {
        before: u32,
        after: u32,
        moved: u32,
    };

    pub fn vacuum(self: *BPTree, mode: VacuumMode) !VacuumStats {
        self.gate.lockUncancelable(self.pool.io);
        defer self.gate.unlock(self.pool.io);
        const before = self.npages;
        const free = try self.gpa.alloc(bool, before);
        defer self.gpa.free(free);
        const list = try self.gpa.alloc(u32, before);
        defer self.gpa.free(list);
        const nfree = try self.markFree(free, list);
        const moved: u32 = switch (mode) {
            .truncate => 0,
            .full => self.moveTail(free, before),
            .incremental => |n| self.moveTail(free, n),
        } catch |err| {
            self.shrink(free, list[0..nfree]) catch {};
            return err;
        };
        try self.shrink(free, list[0..nfree]);
        try self.truncateFile();
        return .{ .before = before, .after = self.npages, .moved = moved };
    }

    pub fn vacuumOnline(self: *BPTree, mode: VacuumMode, step: u32, busy_pct: u32) !VacuumStats {
        std.debug.assert(step > 0 and busy_pct > 0 and busy_pct <= 100);
        const io = self.pool.io;
        if (mode == .truncate) return self.vacuum(.truncate);
        const goal: u32 = if (mode == .incremental) mode.incremental else std.math.maxInt(u32);
        var total: VacuumStats = .{ .before = @atomicLoad(u32, &self.npages, .monotonic), .after = 0, .moved = 0 };
        var cut: u32 = 0;
        while (cut < goal) {
            const start = Io.Clock.Timestamp.now(io, .awake);
            const s = try self.vacuum(.{ .incremental = @min(step, goal - cut) });
            total.moved += s.moved;
            total.after = s.after;
            const ns: u64 = @intCast(start.untilNow(io).raw.toNanoseconds());
            try io.sleep(.fromNanoseconds(@max(std.time.ns_per_ms, ns * (100 - busy_pct) / busy_pct)), .awake);
            if (s.after == s.before) break;
            cut += s.before - s.after;
        }
        return total;
    }

    fn markFree(self: *BPTree, free: []bool, list: []u32) !usize {
        @memset(free, false);
        var n: usize = 0;
        var pg = self.freelist;
        while (pg != 0) : (n += 1) {
            if (pg >= free.len or free[pg]) return error.BadFile;
            free[pg] = true;
            list[n] = pg;
            const p = try self.getPage(pg);
            defer self.pool.unpin(p, .clean);
            if (p.kind() != .free) return error.BadFile;
            pg = p.link();
        }
        return n;
    }

    fn shrink(self: *BPTree, free: []const bool, list: []const u32) !void {
        var end: u32 = @intCast(free.len);
        while (end > 1 and free[end - 1]) end -= 1;
        if (end == free.len) return;
        try self.relinkFree(free, list, end);
        @atomicStore(u32, &self.npages, end, .monotonic);
        try self.syncLocked();
    }

    fn relinkFree(self: *BPTree, free: []const bool, list: []const u32, end: u32) !void {
        const lsn = self.pool.wal.append(self.pool.io, &.{}, 0) catch |err|
            std.debug.panic("vacuum: cannot write the log: {t}", .{err});
        self.freelist = 0;
        var prev: ?usize = null;
        var kept: usize = 0;
        for (list, 0..) |pg, i| {
            if (pg >= end or !free[pg]) continue;
            if (prev) |j| {
                if (j + 1 != i) try self.setFreeLink(list[j], pg, lsn);
            } else self.freelist = pg;
            prev = i;
            kept += 1;
        }
        if (prev) |j| if (j + 1 != list.len) try self.setFreeLink(list[j], 0, lsn);
        std.debug.assert(kept == std.mem.count(bool, free[0..end], &.{true}));
    }

    fn setFreeLink(self: *BPTree, pgno: u32, next: u32, lsn: u64) !void {
        const p = try self.getPage(pgno);
        p.setLink(next);
        self.pool.unpin(p, .{ .logged = lsn });
    }

    fn truncateFile(self: *BPTree) !void {
        const io = self.pool.io;
        const len = @as(u64, self.npages) * page_size;
        if (try self.pool.file.length(io) <= len) return;
        try self.pool.file.setLength(io, len);
        try self.pool.file.sync(io);
    }

    const Owner = struct {
        kind: Kind = .free,
        from: u32 = 0,
        prev: u32 = 0,

        const Kind = enum(u8) {
            free,
            root,
            child,
            chain_first,
            chain_next,
        };
    };

    fn markOwners(self: *BPTree, owners: []Owner, pgno: u32, owner: Owner, last_leaf: *u32, depth: usize) !void {
        if (pgno == meta_pgno or pgno >= owners.len or owners[pgno].kind != .free or depth >= max_depth) return error.BadFile;
        owners[pgno] = owner;
        const p = try self.getPage(pgno);
        defer self.pool.unpin(p, .clean);
        switch (p.kind()) {
            .leaf => {
                owners[pgno].prev = last_leaf.*;
                last_leaf.* = pgno;
                for (0..p.count()) |i| {
                    var from = pgno;
                    var kind: Owner.Kind = .chain_first;
                    var pg = p.overflow(i);
                    while (pg != 0) {
                        if (pg == meta_pgno or pg >= owners.len or owners[pg].kind != .free) return error.BadFile;
                        owners[pg] = .{ .kind = kind, .from = from };
                        const q = try self.getPage(pg);
                        defer self.pool.unpin(q, .clean);
                        if (q.kind() != .overflow) return error.BadFile;
                        from = pg;
                        kind = .chain_next;
                        pg = q.link();
                    }
                }
            },
            .internal => for (0..p.count() + 1) |i|
                try self.markOwners(owners, p.child(i), .{ .kind = .child, .from = pgno }, last_leaf, depth + 1),
            else => return error.BadFile,
        }
    }

    fn moveTail(self: *BPTree, free: []bool, limit: u32) !u32 {
        const owners = try self.gpa.alloc(Owner, free.len);
        defer self.gpa.free(owners);
        @memset(owners, .{});
        var last_leaf: u32 = 0;
        try self.markOwners(owners, self.root, .{ .kind = .root }, &last_leaf, 0);
        var nfree: u32 = 0;
        for (owners[1..], free[1..]) |o, f| {
            if (f != (o.kind == .free)) return error.BadFile;
            if (f) nfree += 1;
        }

        const fin: u32 = @intCast(free.len - @min(limit, nfree));
        var hole: u32 = 1;
        var moved: u32 = 0;
        var last: u32 = @intCast(free.len);
        while (last > fin) {
            last -= 1;
            if (free[last]) continue;
            while (!free[hole]) hole += 1;
            std.debug.assert(hole < fin);
            try self.movePage(owners, last, hole);
            free[hole] = false;
            free[last] = true;
            moved += 1;
        }
        return moved;
    }

    fn movePage(self: *BPTree, owners: []Owner, from: u32, to: u32) !void {
        const o = owners[from];
        const src = try self.getPage(from);
        defer self.pool.unpin(src, .clean);

        var pages: Stack(Page, 3) = .{};
        errdefer for (pages.items()) |p| self.pool.unpin(p, .clean);
        pages.push(try self.pool.pin(to, .no_load));
        var slot: usize = 0;
        if (o.kind != .root) {
            const p = try self.getPage(o.from);
            pages.push(p);
            slot = switch (o.kind) {
                .child => if (p.kind() == .internal) p.childSlot(from) else null,
                .chain_first => if (p.kind() == .leaf) p.overflowSlot(from) else null,
                .chain_next => if (p.kind() == .overflow and p.link() == from) @as(usize, 0) else null,
                else => unreachable,
            } orelse return error.BadFile;
        }
        if (o.prev != 0) {
            const p = try self.getPage(o.prev);
            pages.push(p);
            if (p.kind() != .leaf or p.link() != from) return error.BadFile;
        }

        const dst = pages.buf[0];
        @memcpy(dst.page, src.page);
        switch (o.kind) {
            .root => self.root = to,
            .child => pages.buf[1].setChild(slot, to),
            .chain_first => pages.buf[1].setOverflow(slot, to),
            .chain_next => pages.buf[1].setLink(to),
            .free => unreachable,
        }
        if (o.prev != 0) pages.buf[pages.len - 1].setLink(to);

        owners[to] = o;
        owners[from] = .{};
        switch (dst.kind()) {
            .internal => for (0..dst.count() + 1) |i| {
                owners[dst.child(i)].from = to;
            },
            .leaf => {
                for (0..dst.count()) |i| {
                    const first = dst.overflow(i);
                    if (first != 0) owners[first].from = to;
                }
                if (dst.link() != 0) owners[dst.link()].prev = to;
            },
            .overflow => if (dst.link() != 0) {
                owners[dst.link()].from = to;
            },
            else => unreachable,
        }

        const lsn = self.pool.wal.append(self.pool.io, pages.items(), if (o.kind == .root) to else 0) catch |err|
            std.debug.panic("vacuum: cannot write the log: {t}", .{err});
        for (pages.items()) |p| self.pool.unpin(p, .{ .logged = lsn });
    }

    /// Pins page `pgno`. A page number that is not in the file means that the file is corrupt.
    fn getPage(self: *BPTree, pgno: u32) !Page {
        if (pgno == meta_pgno or pgno >= @atomicLoad(u32, &self.npages, .monotonic)) return error.BadFile;
        return self.pool.pin(pgno, .load);
    }

    fn getPageWith(self: *BPTree, pgno: u32, ring: ?*Ring) !Page {
        if (pgno == meta_pgno or pgno >= @atomicLoad(u32, &self.npages, .monotonic)) return error.BadFile;
        return self.pool.pinWith(pgno, .load, ring);
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
        self.gate.lockSharedUncancelable(self.pool.io);
        defer self.gate.unlockShared(self.pool.io);
        var op: Op = .{};
        const path = try self.descend(&op, key, .read);
        defer self.releaseHeld(&op);
        const leaf = path.leaf();
        const r = leaf.search(key);
        if (r.found) {
            const len = leaf.valLen(r.index);
            if (out.len < len) return error.NoSpaceLeft;
            try self.readValue(leaf, r.index, out[0..len]);
            return out[0..len];
        }
        return null;
    }

    pub fn getAlloc(self: *BPTree, gpa: Allocator, key: []const u8) !?[]u8 {
        if (key.len > max_key) return error.KeyTooLarge;
        self.gate.lockSharedUncancelable(self.pool.io);
        defer self.gate.unlockShared(self.pool.io);
        var op: Op = .{};
        const path = try self.descend(&op, key, .read);
        defer self.releaseHeld(&op);
        const leaf = path.leaf();
        const r = leaf.search(key);
        if (!r.found) return null;
        const out = try gpa.alloc(u8, leaf.valLen(r.index));
        errdefer gpa.free(out);
        try self.readValue(leaf, r.index, out);
        return out;
    }

    fn readValue(self: *BPTree, leaf: Page, i: usize, out: []u8) !void {
        const local = leaf.localVal(i);
        @memcpy(out[0..local.len], local);
        var off = local.len;
        var pg = leaf.overflow(i);
        while (off < out.len) {
            if (pg == 0) return error.BadFile;
            const p = try self.getPage(pg);
            defer self.pool.unpin(p, .clean);
            if (p.kind() != .overflow) return error.BadFile;
            const n = @min(ovfl_cap, out.len - off);
            @memcpy(out[off..][0..n], p.page[hdr_size..][0..n]);
            off += n;
            pg = p.link();
        }
        if (pg != 0) return error.BadFile;
    }

    fn writeChain(self: *BPTree, rest: []const u8) !u32 {
        std.debug.assert(rest.len > 0);
        var prev = try self.pageAlloc(.overflow);
        const first = prev.pgno;
        var off: usize = 0;
        while (true) {
            const n = @min(ovfl_cap, rest.len - off);
            @memcpy(prev.page[hdr_size..][0..n], rest[off..][0..n]);
            off += n;
            if (off < rest.len) {
                const next = self.pageAlloc(.overflow) catch |err| {
                    self.pool.unpin(prev, .dirty);
                    self.freeChain(first, 0) catch {};
                    return err;
                };
                prev.setLink(next.pgno);
                self.logChainPage(prev);
                prev = next;
            } else {
                self.logChainPage(prev);
                return first;
            }
        }
    }

    fn freeChain(self: *BPTree, first: u32, lsn: u64) !void {
        var pg = first;
        while (pg != 0) {
            const p = while (true) break self.getPage(pg) catch |err| switch (err) {
                error.PoolExhausted => {
                    std.Thread.yield() catch {};
                    continue;
                },
                else => return err,
            };
            if (p.kind() != .overflow) {
                self.pool.unpin(p, .clean);
                return error.BadFile;
            }
            pg = p.link();
            p.init(.free);
            self.alloc_mu.lockUncancelable(self.pool.io);
            p.setLink(self.freelist);
            self.freelist = p.pgno;
            self.alloc_mu.unlock(self.pool.io);
            self.pool.unpin(p, .{ .logged = lsn });
        }
    }

    fn logChainPage(self: *BPTree, p: Page) void {
        const lsn = self.pool.wal.append(self.pool.io, &.{p}, 0) catch |err| {
            std.debug.panic("chain: cannot write the log: {t}", .{err});
        };
        self.pool.unpin(p, .{ .logged = lsn });
    }

    /// true if split. The caller holds the path and reserves the new pages.
    fn insertUp(self: *BPTree, op: *Op, path: []const PathEntry, d: usize, idx: usize, c: []const u8) bool {
        std.debug.assert(d >= op.top);
        const p = path[d].page;
        if (p.insertCell(idx, c)) {
            op.markChanged(p);
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
        op.markChanged(right);
        op.markChanged(p);

        if (d == 0) {
            std.debug.assert(op.root_latch == .exclusive);
            const root = takeSpare(op, .internal);
            root.setLink(p.pgno);
            _ = root.insertCell(0, sep);
            self.root = root.pgno;
            op.markChanged(root);
        } else {
            _ = self.insertUp(op, path, d - 1, path[d - 1].idx, sep);
        }
        return true;
    }

    fn putIn(self: *BPTree, op: *Op, key: []const u8, cell: []const u8, how: Descent) !bool {
        var path = try self.descend(op, key, how);
        defer self.finish(op);
        const leaf = path.leaf();
        defer op.releaseSpares();

        const r = leaf.search(key);
        const old_sz = if (r.found) leaf.cell(r.index).len + 2 else 0;
        const new_sz = cell.len + 2;
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
            op.old_chain = leaf.overflow(r.index);
            leaf.deleteCell(r.index);
            op.markChanged(leaf);
        }
        const split = self.insertUp(op, path.slice(), path.depth, r.index, cell);
        std.debug.assert(split == splits);
        if (r.found and !split)
            self.rebalance(op, path.slice(), path.depth);
        return true;
    }

    pub fn put(self: *BPTree, key: []const u8, val: []const u8) !void {
        if (key.len > max_key) return error.KeyTooLarge;
        if (val.len > max_val) return error.ValueTooLarge;
        self.gate.lockSharedUncancelable(self.pool.io);
        defer self.gate.unlockShared(self.pool.io);
        const local = localSize(val.len);
        const first = if (local < val.len) try self.writeChain(val[local..]) else 0;
        var c: [max_leaf_cell]u8 = undefined;
        const cell = if (first == 0) makeLeafCell(&c, key, val) else makeOverflowCell(&c, key, val.len, val[0..local], first);
        var op: Op = .{};
        self.putCell(&op, key, cell) catch |err| {
            if (first != 0) try self.freeChain(first, 0);
            return err;
        };
        if (op.old_chain != 0) try self.freeChain(op.old_chain, op.lsn);
        if (self.durable) try self.pool.wal.flushTo(self.pool.io, op.lsn);
    }

    fn putCell(self: *BPTree, op: *Op, key: []const u8, cell: []const u8) !void {
        if (!try self.putIn(op, key, cell, .optimistic))
            _ = try self.putIn(op, key, cell, .write);
    }

    /// The caller holds the path and the siblings, and reserves the new pages.
    fn rebalance(self: *BPTree, op: *Op, path: []const PathEntry, d: usize) void {
        std.debug.assert(d >= op.top);
        const p = path[d].page;

        if (d == 0) {
            if (p.kind() == .internal and p.count() == 0) {
                std.debug.assert(op.root_latch == .exclusive);
                self.root = p.link();
                op.pageFree(p);
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
            op.pageFree(right);
            op.markChanged(left);
            parent.deleteCell(sep_idx);
            op.markChanged(parent);
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
        op.markChanged(left);
        op.markChanged(right);
        parent.deleteCell(sep_idx);
        op.markChanged(parent);

        if (!self.insertUp(op, path, d - 1, sep_idx, sep)) {
            self.rebalance(op, path, d - 1);
        }
    }

    fn deleteIn(self: *BPTree, op: *Op, key: []const u8, how: Descent) !?bool {
        var path = try self.descend(op, key, how);
        defer self.finish(op);
        const leaf = path.leaf();
        defer op.releaseSpares();

        const r = leaf.search(key);
        if (!r.found) return false;
        const old_sz = leaf.cell(r.index).len + 2;
        if (leaf.usedBytes() - old_sz < min_fill) {
            if (how == .optimistic) return null;
            try self.reserve(op, try self.holdSiblings(op, path.slice(), path.depth));
        } else {
            self.releaseAbove(op);
        }

        op.old_chain = leaf.overflow(r.index);
        leaf.deleteCell(r.index);
        op.markChanged(leaf);
        self.rebalance(op, path.slice(), path.depth);
        return true;
    }

    pub fn delete(self: *BPTree, key: []const u8) !bool {
        if (key.len > max_key) return error.KeyTooLarge;
        self.gate.lockSharedUncancelable(self.pool.io);
        defer self.gate.unlockShared(self.pool.io);
        var op: Op = .{};
        const found = try self.deleteIn(&op, key, .optimistic) orelse (try self.deleteIn(&op, key, .write)).?;
        if (op.old_chain != 0) try self.freeChain(op.old_chain, op.lsn);
        if (self.durable) try self.pool.wal.flushTo(self.pool.io, op.lsn);
        return found;
    }

    /// The key and value slices are valid only during the call to `visit`. `visit` must not call the tree:
    /// the scan holds the gate, and a second hold of it waits for a `vacuum` that waits for the scan.
    pub fn scan(
        self: *BPTree,
        lo: ?[]const u8,
        hi: ?[]const u8,
        ctx: anytype,
        comptime visit: fn (ctx: @TypeOf(ctx), key: []const u8, val: []const u8) anyerror!void,
    ) !usize {
        self.gate.lockSharedUncancelable(self.pool.io);
        defer self.gate.unlockShared(self.pool.io);
        var start_buf: [max_key]u8 = undefined;
        var start: []const u8 = lo orelse "";
        var after: bool = false;
        var count: usize = 0;
        var ring: Ring = .{};
        var big: []u8 = &.{};
        defer self.gpa.free(big);
        const use_ring = build_options.scan_ring and ring_frames > 0 and @atomicLoad(u32, &self.npages, .monotonic) > pool_frames / 4;

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
                    const val = if (leaf.overflow(j) == 0) leaf.localVal(j) else blk: {
                        const len = leaf.valLen(j);
                        if (big.len < len) {
                            self.gpa.free(big);
                            big = &.{};
                            big = try self.gpa.alloc(u8, len);
                        }
                        try self.readValue(leaf, j, big[0..len]);
                        break :blk big[0..len];
                    };
                    try visit(ctx, k, val);
                    count += 1;
                }
                const next = leaf.link();
                if (next == 0) return count;
                const p = try self.getPageWith(next, if (use_ring) &ring else null);
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

    pub fn check(self: *BPTree) !void {
        const seen = try self.gpa.alloc(bool, self.npages);
        defer self.gpa.free(seen);
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
                for (0..n) |i| try self.checkChain(st, p.overflow(i), p.valLen(i) - p.localVal(i).len);
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

    fn checkChain(self: *BPTree, st: *CheckState, first: u32, rest: usize) !void {
        var pg = first;
        var left = rest;
        while (left > 0) {
            if (pg == 0) return checkFail("a chain ends {d} bytes early", .{left});
            if (pg == meta_pgno or pg >= self.npages or st.seen[pg])
                return checkFail("overflow page {d} is out of range or seen twice", .{pg});
            st.seen[pg] = true;
            const p = try self.getPage(pg);
            defer self.pool.unpin(p, .clean);
            if (p.kind() != .overflow) return checkFail("page {d} is in a chain but has type {d}", .{ pg, @backingInt(p.kind()) });
            left -= @min(left, ovfl_cap);
            pg = p.link();
        }
        if (pg != 0) return checkFail("a chain is longer than its value", .{});
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
        overflow = 3,
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
        if (self.kind() == .leaf) return leafCellSize(get16(c), get32(c[2..]));
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
            return c[6..][0..klen];
        } else {
            const klen = get16(c[4..]);
            return c[6..][0..klen];
        }
    }

    fn valLen(self: Page, i: usize) u32 {
        return get32(self.cell(i)[2..]);
    }
    fn localVal(self: Page, i: usize) []const u8 {
        const c = self.cell(i);
        return c[6 + get16(c) ..][0..localSize(get32(c[2..]))];
    }
    fn overflow(self: Page, i: usize) u32 {
        const c = self.cell(i);
        if (get32(c[2..]) <= max_local) return 0;
        return get32(c[c.len - 4 ..]);
    }

    fn overflowSlot(self: Page, pgno: u32) ?usize {
        for (0..self.count()) |i| if (self.overflow(i) == pgno) return i;
        return null;
    }
    fn setOverflow(self: Page, i: usize, pgno: u32) void {
        std.debug.assert(self.overflow(i) != 0);
        const end = self.slot(i) + self.cell(i).len;
        put32(self.page[end - 4 ..], pgno);
    }

    fn child(self: Page, i: usize) u32 {
        return if (i == 0) self.link() else get32(self.cell(i - 1));
    }

    fn childSlot(self: Page, pgno: u32) ?usize {
        for (0..self.count() + 1) |i| if (self.child(i) == pgno) return i;
        return null;
    }
    fn setChild(self: Page, i: usize, pgno: u32) void {
        if (i == 0) self.setLink(pgno) else put32(self.page[self.slot(i - 1)..], pgno);
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

fn localSize(vlen: usize) usize {
    if (vlen <= max_local) return vlen;
    const k = min_local + (vlen - min_local) % ovfl_cap;
    return if (k <= max_local) k else min_local;
}

fn leafCellSize(klen: usize, vlen: usize) usize {
    const ptr: usize = if (vlen > max_local) 4 else 0;
    return 6 + klen + localSize(vlen) + ptr;
}

fn makeLeafCell(out: []u8, k: []const u8, v: []const u8) []u8 {
    std.debug.assert(v.len <= max_local);
    put16(out, @intCast(k.len));
    put32(out[2..], @intCast(v.len));
    @memcpy(out[6..][0..k.len], k);
    @memcpy(out[6 + k.len ..][0..v.len], v);
    return out[0 .. 6 + k.len + v.len];
}

fn makeOverflowCell(out: []u8, k: []const u8, vlen: usize, local: []const u8, first: u32) []u8 {
    std.debug.assert(vlen > max_local and local.len == localSize(vlen) and first != 0);
    put16(out, @intCast(k.len));
    put32(out[2..], @intCast(vlen));
    @memcpy(out[6..][0..k.len], k);
    @memcpy(out[6 + k.len ..][0..local.len], local);
    put32(out[6 + k.len + local.len ..], first);
    return out[0 .. 6 + k.len + local.len + 4];
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

fn createTestLog(dir: Io.Dir) ![2]Io.File {
    const a = try dir.createFile(std.testing.io, "test.bin.wal0", .{ .read = true });
    errdefer a.close(std.testing.io);
    return .{ a, try dir.createFile(std.testing.io, "test.bin.wal1", .{ .read = true }) };
}

fn closeTestLog(log: [2]Io.File) void {
    for (log) |f| f.close(std.testing.io);
}

test BPTree {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

    try t.metaWrite(.{ .epoch = 5, .root = 1, .npages = 2, .freelist = 0 });
    try t.metaRead();
    try std.testing.expectEqual(5, t.pool.wal.epoch);
    // The newer of the two copies wins, and a torn copy is ignored.
    try t.metaWrite(.{ .epoch = 6, .root = 1, .npages = 2, .freelist = 0 });
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
    var out: [max_local]u8 = undefined;
    const N = 500;
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    {
        var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
        defer t.deinit();
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        try t.sync();
    }
    // A new tree has an empty pool, so it reads all pages from the file.
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
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
    defer closeTestLog(log);

    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
    const N = 2000;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit();
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        for (0..N) |i| {
            if (i % 3 == 0) _ = try t.delete(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}));
        }
        // No sync: deinit drops the pool, as a crash would. Some pages reached the file and some did not.
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();
    try t.check();
    for (0..N) |i| {
        const got = try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out);
        if (i % 3 == 0) try std.testing.expectEqual(null, got) else try std.testing.expectEqualStrings("value", got.?);
    }
}

test "BPTree sync starts a new run and empties the file of the run before" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();

    var kbuf: [16]u8 = undefined;
    for (0..3) |_| {
        const e = t.pool.wal.epoch;
        for (0..100) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        try std.testing.expect(try log[e % 2].length(io) > 0);
        try t.sync();
        // The new run is in the other file. The file of run `e` is empty, and so is the new run.
        try std.testing.expectEqual(e + 1, t.pool.wal.epoch);
        try std.testing.expectEqual(0, try log[e % 2].length(io));
        try std.testing.expectEqual(t.pool.wal.start.raw, t.pool.wal.end.raw);
        try std.testing.expectEqual(0, try log[(e + 1) % 2].length(io));
        try t.metaRead();
        try std.testing.expectEqual(e + 1, t.pool.wal.epoch);
    }
}

/// Puts keys 0 to `n` - 1 into `t`, with `val` as value.
fn testPut(t: *BPTree, n: usize, val: []const u8) !void {
    var kbuf: [16]u8 = undefined;
    for (0..n) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), val);
}

/// Checks that `t` is whole and holds keys 0 to `n` - 1 with `val` as value.
fn testExpect(t: *BPTree, n: usize, val: []const u8) !void {
    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
    try t.check();
    for (0..n) |i| try std.testing.expectEqualStrings(val, (try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out)).?);
}

test "BPTree recovery reads the run after a checkpoint that did not end" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    const N = 1000;
    var e: u32 = undefined;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit();
        e = t.pool.wal.epoch;
        try testPut(&t, N, "one");
        // A checkpoint starts run e + 1, and then the process crashes before the meta page.
        _ = try t.pool.wal.nextRun(io);
        try testPut(&t, N, "two");
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();
    try testExpect(&t, N, "two");
    // The meta page is in the slot that run e did not use, so a torn write of it leaves the meta page of run e.
    const now = t.pool.wal.epoch;
    try std.testing.expect(now > e + 1 and now % 2 != e % 2);
    try t.metaRead();
    try std.testing.expectEqual(now, t.pool.wal.epoch);
}

test "BPTree recovery never joins old records of a run" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    const N = 20;
    var old: []u8 = undefined;
    var f: usize = undefined;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit();
        try testPut(&t, N, "one");
        const off = t.pool.wal.end.raw - t.pool.wal.start.raw;
        const prev = t.pool.wal.file();
        // A checkpoint starts run e + 1 and logs two operations into it: a harmless page, and then a page that
        // would break the tree. Then the `.next` record is torn, so recovery ignores run e + 1.
        _ = try t.pool.wal.nextRun(io);
        var zero: [page_size]u8 = @splat(0);
        _ = try t.pool.wal.append(io, &.{.{ .page = &zero, .pgno = t.npages + 3 }}, 0);
        var junk: [page_size]u8 = @splat(0xEE);
        _ = try t.pool.wal.append(io, &.{.{ .page = &junk, .pgno = t.root }}, 0);
        try prev.writePositionalAll(io, "x", off + 10);
        f = t.pool.wal.epoch % 2;
        old = try std.testing.allocator.alloc(u8, try log[f].length(io));
        _ = try log[f].readPositionalAll(io, old, 0);
    }
    defer std.testing.allocator.free(old);
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit();
        try testExpect(&t, N, "one");
        // Recovery emptied that file. A power cut can lose that cut and leave the old records there.
        try log[f].writePositionalAll(io, old, 0);
        // One put logs one page and a commit, as the harmless operation did, so its records end where the
        // junk starts. A record of the new run must not be followed by an old record.
        try t.put("key00000000", "two");
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();
    try t.check();
    var out: [max_local]u8 = undefined;
    try std.testing.expectEqualStrings("two", (try t.get("key00000000", &out)).?);
}

test "BPTree recovery stops at a torn next record" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    const N = 1000;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit();
        try testPut(&t, N, "one");
        const off = t.pool.wal.end.raw - t.pool.wal.start.raw;
        const old = t.pool.wal.file();
        _ = try t.pool.wal.nextRun(io);
        // Run e + 1 has an operation that would break the tree. Recovery must not reach it.
        var junk: [page_size]u8 = @splat(0xEE);
        _ = try t.pool.wal.append(io, &.{.{ .page = &junk, .pgno = t.root }}, 0);
        try old.writePositionalAll(io, "x", off + 10);
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();
    try testExpect(&t, N, "one");
}

test "BPTree recovers values with chains after a crash" {
    const io = std.testing.io;
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);

    const N = 60;
    const lens = [_]usize{ 20, max_local + 1, 2 * ovfl_cap + 7 };
    const vbuf = try gpa.alloc(u8, lens[2]);
    defer gpa.free(vbuf);
    const out = try gpa.alloc(u8, lens[2]);
    defer gpa.free(out);
    var kbuf: [16]u8 = undefined;
    {
        var t: BPTree = try .init(gpa, io, file, log);
        defer t.deinit();
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), testValue(vbuf, lens[i % 3], 1));
        try t.sync();
        // After the sync: replace a third, delete a third. Old chains go to the free list, new chains come from it.
        for (0..N) |i| {
            const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
            if (i % 3 == 0) try t.put(k, testValue(vbuf, lens[(i + 2) % 3], 2));
            if (i % 3 == 1) _ = try t.delete(k);
        }
        // An orphan chain: the crash came after its pages were logged, but before the put of its cell.
        _ = try t.writeChain(testValue(vbuf, lens[2], 9));
        // No sync: deinit drops the pool, as a crash would.
    }
    var t: BPTree = try .init(gpa, io, file, log);
    defer t.deinit();
    // The orphan chain is on the free list, and no page of a live chain is.
    try t.check();
    for (0..N) |i| {
        const got = try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), out);
        switch (i % 3) {
            0 => try std.testing.expectEqualSlices(u8, testValue(vbuf, lens[(i + 2) % 3], 2), got.?),
            1 => try std.testing.expectEqual(null, got),
            else => try std.testing.expectEqualSlices(u8, testValue(vbuf, lens[i % 3], 1), got.?),
        }
    }
}

test "BPTree freed chain page waits for the commit that freed it" {
    if (build_options.pool_paranoid) return error.SkipZigTest;
    const io = std.testing.io;
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(gpa, io, file, log);
    defer t.deinit();

    const big: [2 * ovfl_cap]u8 = @splat('b');
    try t.put("k", &big);
    try t.sync();
    var op: Op = .{};
    const path = try t.descend(&op, "k", .read);
    const old = path.leaf().overflow(0);
    t.releaseHeld(&op);

    // The replace frees the old chain. Its commit is in the log, but not durable.
    t.durable = false;
    try t.put("k", "small");
    try std.testing.expect(t.pool.wal.end.raw > t.pool.wal.durable.raw);
    // The two pages of the old chain are at the head of the free list, the second page first.
    // An eviction of either must first make the commit durable, so each carries the LSN of the commit.
    const second = t.freelist;
    for ([_]u32{ old, second }) |pg| {
        try std.testing.expectEqual(t.pool.wal.end.raw, t.pool.frames[t.pool.find(pg).?].lsn.raw);
        const p = try t.getPage(pg);
        defer t.pool.unpin(p, .clean);
        try std.testing.expectEqual(.free, p.kind());
        if (pg == second) try std.testing.expectEqual(old, p.link());
    }
    try t.check();
    try t.sync();
}

test "BPTree recovery ignores an operation that did not commit" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);

    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
    const N = 500;
    {
        var t: BPTree = try .init(std.testing.allocator, io, file, log);
        defer t.deinit();
        for (0..N) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), "value");
        // An operation that crashed after it logged an image of the root, but before its commit record.
        var junk: [page_size]u8 = @splat(0xEE);
        const end = try t.pool.wal.append(io, &.{.{ .page = &junk }}, 0);
        try t.pool.wal.file().setLength(io, end - t.pool.wal.start.raw - Wal.rec_hdr);
    }
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();
    try t.check();
    for (0..N) |i| try std.testing.expectEqualStrings("value", (try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out)).?);
}

test "BPTree bad file" {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    try file.writePositionalAll(io, "garbage!", 0);
    try std.testing.expectError(error.BadFile, BPTree.init(std.testing.allocator, io, file, log));
}

test Wal {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var w: Wal = .{ .files = log, .epoch = 7 };

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
        const r = (try w.read(io, 7, off, &buf)).?;
        try std.testing.expectEqual(wnt[0], r.kind);
        try std.testing.expectEqual(wnt[1], r.arg);
        if (r.kind == .page) try std.testing.expectEqual(wnt[2], buf[100]);
        off = r.end;
    }
    try std.testing.expectEqual(second, off);
    try std.testing.expectEqual(null, try w.read(io, 7, off, &buf));

    // A new run starts at offset 0 of the other file. The LSNs go on.
    const start = try w.nextRun(io);
    try std.testing.expectEqual(second + Wal.rec_hdr, start);
    try std.testing.expectEqual(8, w.epoch);
    const third = try w.append(io, &.{pb}, 0);
    try std.testing.expectEqual(start + Wal.rec_hdr + page_size + Wal.rec_hdr, third);

    // `LogPos` reads run 7 up to its `.next` record, and then run 8.
    var pos: LogPos = .{ .epoch = 7 };
    const all = [_]struct { Wal.Kind, u32 }{
        .{ .page, 3 }, .{ .page, 4 }, .{ .commit, 0 }, .{ .page, 5 }, .{ .commit, 9 }, .{ .next, 8 }, .{ .page, 4 }, .{ .commit, 0 },
    };
    for (all) |wnt| {
        const r = (try pos.next(&w, io, &buf)).?;
        try std.testing.expectEqual(wnt[0], r.kind);
        try std.testing.expectEqual(wnt[1], r.arg);
    }
    try std.testing.expectEqual(null, try pos.next(&w, io, &buf));
    try std.testing.expectEqual(LogPos{ .epoch = 8, .off = third - start }, pos);

    // A torn record ends the run there, and the log with it: run 8 is not reached.
    try log[1].writePositionalAll(io, "x", first + Wal.rec_hdr + 100);
    try std.testing.expectEqual(null, try w.read(io, 7, first, &buf));
    pos = .{ .epoch = 7 };
    for (0..3) |_| _ = (try pos.next(&w, io, &buf)).?;
    try std.testing.expectEqual(null, try pos.next(&w, io, &buf));
    try std.testing.expectEqual(LogPos{ .epoch = 7, .off = first }, pos);

    // A record of another run ends it too.
    try std.testing.expectEqual(null, try w.read(io, 9, 0, &buf));
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
    try std.testing.expectEqualStrings("value", leaf.localVal(2));

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

test localSize {
    // A value up to max_local stays whole. One byte more, and the cell keeps only min_local bytes.
    try std.testing.expectEqual(0, localSize(0));
    try std.testing.expectEqual(max_local, localSize(max_local));
    try std.testing.expectEqual(min_local, localSize(max_local + 1));
    // 10 bytes more than min_local plus one full page: the cell keeps the 10 bytes, so the page is full.
    try std.testing.expectEqual(min_local + 10, localSize(min_local + ovfl_cap + 10));
    // In all cases the cell keeps min_local to max_local bytes, and the overflow pages are full or the cell keeps min_local.
    for (max_local + 1..max_local + 3 * ovfl_cap) |vlen| {
        const local = localSize(vlen);
        try std.testing.expect(local >= min_local and local <= max_local);
        try std.testing.expect((vlen - local) % ovfl_cap == 0 or local == min_local);
    }
}

test "Page leaf cell with overflow" {
    var buf: [page_size]u8 = undefined;
    var cell: [max_leaf_cell]u8 = undefined;
    const leaf: Page = .{ .page = &buf };
    leaf.init(.leaf);

    const vlen = 3 * ovfl_cap;
    const local: [localSize(vlen)]u8 = @splat('L');
    const c = makeOverflowCell(&cell, "big", vlen, &local, 77);
    try std.testing.expectEqual(leafCellSize(3, vlen), c.len);
    try std.testing.expect(leaf.insertCell(0, makeLeafCell(cell[c.len..], "a", "small")));
    try std.testing.expect(leaf.insertCell(1, c));

    try std.testing.expectEqualStrings("a", leaf.cellKey(0));
    try std.testing.expectEqual(5, leaf.valLen(0));
    try std.testing.expectEqualStrings("small", leaf.localVal(0));
    try std.testing.expectEqual(0, leaf.overflow(0));

    try std.testing.expectEqualStrings("big", leaf.cellKey(1));
    try std.testing.expectEqual(vlen, leaf.valLen(1));
    try std.testing.expectEqualStrings(&local, leaf.localVal(1));
    try std.testing.expectEqual(77, leaf.overflow(1));
    // The pointer moves with the cell.
    leaf.deleteCell(0);
    leaf.compact();
    try std.testing.expectEqual(77, leaf.overflow(0));
}

test Pool {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

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

/// A pin and unpin of page `pgno` by a scan with `ring`, with no I/O. Returns the frame.
fn testRingPin(pool: *Pool, pgno: u32, ring: *Ring) !usize {
    const p = try pool.pinWith(pgno, .no_load, ring);
    defer pool.unpin(p, .clean);
    return pool.frameIndex(p);
}

test "Pool ring" {
    // With a max_usage of 1, a ring cannot see that another reader used one of its frames.
    if (build_options.pool_paranoid or ring_frames < 2 or max_usage < 2) return error.SkipZigTest;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
    testEmptyPool(&t);
    const pool = &t.pool;

    // The first misses of a scan fill the ring from the clock sweep. Then the scan reuses the ring.
    var ring: Ring = .{};
    var used: [pool_frames]bool = @splat(false);
    const moves = pool.hand.raw;
    for (1..3 * ring_frames + 1) |pg| used[try testRingPin(pool, @intCast(pg), &ring)] = true;
    try std.testing.expectEqual(ring_frames, std.mem.count(bool, &used, &.{true}));
    for (ring.slots) |slot| try std.testing.expect(used[slot.?]);
    try std.testing.expectEqual(ring_frames, pool.hand.raw - moves);

    // A hit through the ring raises a usage count of 0 to 1, and no higher.
    const pg: u32 = 3 * ring_frames;
    const fr = &pool.frames[pool.find(pg).?];
    testSetUsage(fr, 0);
    _ = try testRingPin(pool, pg, &ring);
    try std.testing.expectEqual(1, fr.load().usage);
    _ = try testRingPin(pool, pg, &ring);
    try std.testing.expectEqual(1, fr.load().usage);

    // Another reader uses the page in the next slot. The scan does not take that frame:
    // it gets a new frame the normal way, and the new frame takes the slot.
    const next = (ring.current + 1) % ring_frames;
    const other = ring.slots[next].?;
    try testPin(pool, pool.frames[other].pgno.?);
    const f = try testRingPin(pool, 100, &ring);
    try std.testing.expect(f != other);
    try std.testing.expectEqual(f, ring.slots[next].?);
    try std.testing.expect(pool.frames[other].pgno != null);
}

test "Pool ring drops a frame whose write must force the log" {
    if (build_options.pool_paranoid or ring_frames < 2) return error.SkipZigTest;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
    testEmptyPool(&t);
    const pool = &t.pool;

    var ring: Ring = .{};
    for (1..ring_frames + 1) |pg| _ = try testRingPin(pool, @intCast(pg), &ring);
    // The page in the next slot changes, and its log record is not on disk yet.
    const next = (ring.current + 1) % ring_frames;
    const f = ring.slots[next].?;
    const pgno = pool.frames[f].pgno.?;
    testSetDirty(&pool.frames[f], true);
    pool.frames[f].lsn.store(try pool.wal.append(std.testing.io, &.{}, 0), .monotonic);

    // The scan drops the frame from its ring and takes the frame in the slot after it. Nothing is written.
    const writes = pool.writes.raw;
    const g = try testRingPin(pool, 100, &ring);
    try std.testing.expect(g != f);
    try std.testing.expectEqual(null, ring.slots[next]);
    try std.testing.expectEqual(pgno, pool.frames[f].pgno.?);
    try std.testing.expect(pool.frames[f].load().dirty);
    try std.testing.expectEqual(writes, pool.writes.raw);
    // Leave the pool clean for deinit.
    testSetDirty(&pool.frames[f], false);
}

test "BPTree large scan keeps a hot path in the pool" {
    // A scan holds two leaves at a time, so a ring of one frame cannot reuse its frame.
    if (build_options.pool_paranoid or !build_options.scan_ring or ring_frames < 2) return error.SkipZigTest;
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, io, file, log);
    defer t.deinit();

    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
    const val: [@min(100, max_local)]u8 = @splat('v');
    var n: usize = 0;
    while (t.npages < 4 * pool_frames) : (n += 1) {
        try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{n}), &val);
    }
    const hot = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{n / 2});
    for (0..3) |_| _ = (try t.get(hot, &out)).?;

    // The scan reads every leaf, many more pages than the pool holds.
    const Count = struct {
        fn visit(_: void, _: []const u8, _: []const u8) !void {}
    };
    try std.testing.expectEqual(n, try t.scan(null, null, {}, Count.visit));
    // The path of the hot key is still in the pool.
    const reads = t.pool.reads.raw;
    _ = (try t.get(hot, &out)).?;
    try std.testing.expectEqual(reads, t.pool.reads.raw);
}

test "BPTree page alloc" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

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
    op.pageFree(a);
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

/// Sets the dirty flag of a frame that no other thread uses.
fn testSetDirty(fr: *Frame, dirty: bool) void {
    var s = fr.load();
    s.dirty = dirty;
    fr.state.store(@bitCast(s), .monotonic);
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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

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

    var buf: [max_local]u8 = undefined;
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
    try std.testing.expectEqual(4 * (6 + 1 + 5 + 2), cl.bytes(0, cl.cells.len));

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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

    const N = 2000;
    var order: [N]usize = undefined;
    for (&order, 0..) |*o, i| o.* = i;
    var prng: std.Random.DefaultPrng = .init(42);
    prng.random().shuffle(usize, &order);

    var kbuf: [16]u8 = undefined;
    var vbuf: [32]u8 = undefined;
    var out: [max_local]u8 = undefined;

    for (order) |i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        const v = try std.fmt.bufPrint(&vbuf, "value-{d}-xxxxxxxxxxxxxxxx", .{i});
        try t.put(k, v);
    }
    try std.testing.expectEqual(0, t.pool.pinned());
    try std.testing.expect(t.npages > 2);
    try t.check();

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
    try t.check();

    const root = try t.getPage(t.root);
    defer t.pool.unpin(root, .clean);
    try std.testing.expectEqual(.leaf, root.kind());
    try std.testing.expectEqual(0, root.count());
}

/// A value of `len` bytes that depends on `seed`, so a test can tell values apart and see where one goes wrong.
fn testValue(buf: []u8, len: usize, seed: u8) []u8 {
    for (buf[0..len], 0..) |*b, i| b.* = @truncate(i *% 31 +% i / ovfl_cap +% seed);
    return buf[0..len];
}

test "BPTree large values" {
    const io = std.testing.io;
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);

    // Lengths around each edge, and one chain longer than the pool.
    const lens = [_]usize{ 0, 1, max_local, max_local + 1, min_local + ovfl_cap, min_local + ovfl_cap + 1, 3 * ovfl_cap, (pool_frames + 3) * ovfl_cap + 5 };
    const vbuf = try gpa.alloc(u8, lens[lens.len - 1]);
    defer gpa.free(vbuf);
    const out = try gpa.alloc(u8, lens[lens.len - 1]);
    defer gpa.free(out);
    var kbuf: [16]u8 = undefined;
    {
        var t: BPTree = try .init(gpa, io, file, log);
        defer t.deinit();
        for (lens, 0..) |len, i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), testValue(vbuf, len, @intCast(i)));
        try t.check();
        // Each chain has just enough pages: the root leaf and the chains are all the pages of the tree.
        var chain_pages: usize = 0;
        for (lens) |len| chain_pages += std.math.divCeil(usize, len - localSize(len), ovfl_cap) catch unreachable;
        try std.testing.expectEqual(2 + chain_pages, t.npages);
        try t.sync();
    }
    // A new tree reads all pages from the file.
    var t: BPTree = try .init(gpa, io, file, log);
    defer t.deinit();
    for (lens, 0..) |len, i| {
        const k = try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i});
        const want = testValue(vbuf, len, @intCast(i));
        try std.testing.expectEqualSlices(u8, want, (try t.get(k, out)).?);
        const got = (try t.getAlloc(gpa, k)).?;
        defer gpa.free(got);
        try std.testing.expectEqualSlices(u8, want, got);
        if (len > 0) try std.testing.expectError(error.NoSpaceLeft, t.get(k, out[0 .. len - 1]));
    }
    try std.testing.expectEqual(null, try t.getAlloc(gpa, "nokey"));

    const Check = struct {
        lens: []const usize,
        buf: []u8,
        n: usize = 0,
        fn visit(c: *@This(), _: []const u8, val: []const u8) !void {
            try std.testing.expectEqualSlices(u8, testValue(c.buf, c.lens[c.n], @intCast(c.n)), val);
            c.n += 1;
        }
    };
    var c: Check = .{ .lens = &lens, .buf = vbuf };
    try std.testing.expectEqual(lens.len, try t.scan(null, null, &c, Check.visit));
    try std.testing.expectEqual(0, t.pool.pinned());
}

test "BPTree replace and delete free chains" {
    const io = std.testing.io;
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(gpa, io, file, log);
    defer t.deinit();

    const lens = [_]usize{ 10, max_local + 1, 2 * ovfl_cap, 5 * ovfl_cap };
    const vbuf = try gpa.alloc(u8, lens[lens.len - 1]);
    defer gpa.free(vbuf);
    const out = try gpa.alloc(u8, lens[lens.len - 1]);
    defer gpa.free(out);
    var kbuf: [16]u8 = undefined;
    const keys = 20;

    // All keys get the longest value first. Then a replace frees the old chain after it writes the new one,
    // so the file grows by one chain at most, however many times the values change.
    for (0..keys) |i| try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), testValue(vbuf, lens[3], 0));
    const npages = t.npages;
    var prng: std.Random.DefaultPrng = .init(1);
    var cur: [keys]usize = @splat(3);
    for (1..20) |round| {
        for (0..keys) |i| {
            cur[i] = prng.random().uintLessThan(usize, lens.len);
            try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), testValue(vbuf, lens[cur[i]], @intCast(round)));
        }
        try t.check();
        for (0..keys) |i| {
            const got = (try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), out)).?;
            try std.testing.expectEqualSlices(u8, testValue(vbuf, lens[cur[i]], @intCast(round)), got);
        }
    }
    try std.testing.expect(t.npages <= npages + 5 + 2);

    // After the deletes, every page but the root leaf is on the free list.
    for (0..keys) |i| try std.testing.expect(try t.delete(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i})));
    try t.check();
    var free: usize = 0;
    var pg = t.freelist;
    while (pg != 0) : (free += 1) {
        const p = try t.getPage(pg);
        defer t.pool.unpin(p, .clean);
        pg = p.link();
    }
    try std.testing.expectEqual(t.npages - 2, free);
}

test "BPTree failed put frees its new chain" {
    if (pool_frames < 4) return error.SkipZigTest;
    const io = std.testing.io;
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(gpa, io, file, log);
    defer t.deinit();

    // Fill the root leaf with small values, so that the cell of the big value splits it.
    const huge: [3 * ovfl_cap]u8 = @splat('h');
    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
    const val: [8]u8 = @splat('v');
    var n: usize = 0;
    while (true) : (n += 1) {
        const root = try t.getPage(t.root);
        const full = root.freeBytes() < leafCellSize(3, huge.len) + 2;
        t.pool.unpin(root, .clean);
        if (full) break;
        try t.put(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{n}), &val);
    }

    // Leave two frames free: enough to write a chain, but not enough for the root, the new leaf and the new root.
    var pinned: [pool_frames]Page = undefined;
    for (pinned[0 .. pool_frames - 2], 0..) |*p, i| p.* = try t.pool.pin(@intCast(1000 + i), .no_load);
    const npages = t.npages;
    try std.testing.expectError(error.PoolExhausted, t.put("zzz", &huge));
    for (pinned[0 .. pool_frames - 2]) |p| t.pool.unpin(p, .clean);

    // The chain was written: the file grew. Its pages are on the free list, and the tree is as it was.
    try std.testing.expect(t.npages >= npages + 3);
    try t.check();
    try std.testing.expectEqual(null, try t.get("zzz", &out));
    for (0..n) |i| try std.testing.expectEqualStrings(&val, (try t.get(try std.fmt.bufPrint(&kbuf, "key{d:0>8}", .{i}), &out)).?);
}

test "BPTree scan" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const file = try createTestFile(tmp.dir);
    defer file.close(std.testing.io);
    const log = try createTestLog(tmp.dir);
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();

    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
    const big: [max_local]u8 = @splat('v');

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
    defer closeTestLog(log);
    var t: BPTree = try .init(std.testing.allocator, std.testing.io, file, log);
    defer t.deinit();
    t.durable = false;

    var kbuf: [16]u8 = undefined;
    var out: [max_local]u8 = undefined;
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

/// A tree for the vacuum tests, in a file of a test directory.
const VacTest = struct {
    tmp: std.testing.TmpDir,
    file: Io.File,
    log: [2]Io.File,
    t: BPTree,
    vbuf: []u8,
    out: []u8,

    const gpa = std.testing.allocator;
    const io = std.testing.io;

    fn init(self: *VacTest) !void {
        self.tmp = std.testing.tmpDir(.{});
        self.file = try createTestFile(self.tmp.dir);
        self.log = try createTestLog(self.tmp.dir);
        self.t = try .init(gpa, io, self.file, self.log);
        self.vbuf = try gpa.alloc(u8, 4 * ovfl_cap);
        self.out = try gpa.alloc(u8, 4 * ovfl_cap);
    }

    fn deinit(self: *VacTest) void {
        self.t.deinit();
        gpa.free(self.vbuf);
        gpa.free(self.out);
        self.file.close(io);
        closeTestLog(self.log);
        self.tmp.cleanup();
    }

    /// Drops the pool, as a crash would, and opens the tree again.
    fn crash(self: *VacTest) !void {
        self.t.deinit();
        self.t = try .init(gpa, io, self.file, self.log);
    }

    fn fileLen(self: *VacTest) !u64 {
        return self.file.length(io);
    }

    fn freePages(self: *VacTest) !u32 {
        var n: u32 = 0;
        var pg = self.t.freelist;
        while (pg != 0) : (n += 1) {
            const p = try self.t.getPage(pg);
            defer self.t.pool.unpin(p, .clean);
            pg = p.link();
        }
        return n;
    }

    /// Long keys, so that the tree has more levels and many internal pages. A pool of a few frames
    /// cannot hold the path of a deep tree, so there the keys are short.
    const key_len = if (pool_frames >= 16) @min(200, max_key) else 16;

    fn key(buf: *[key_len]u8, i: usize) []const u8 {
        @memset(buf, 'k');
        _ = std.fmt.bufPrint(buf, "{d:0>8}", .{i}) catch unreachable;
        return buf;
    }

    /// Puts keys `0..n`, and then deletes the keys that `keep` rejects, in a random order.
    /// Before the keys, a value with a chain of 128 pages takes the start of the file. Its delete at the end
    /// frees those pages, so that the root and the other pages of the tree are near the end of the file.
    fn fill(self: *VacTest, n: usize, comptime keep: fn (usize) bool) !void {
        const front = try gpa.alloc(u8, 128 * ovfl_cap);
        defer gpa.free(front);
        try self.t.put("!", testValue(front, front.len, 0));
        defer _ = self.t.delete("!") catch unreachable;
        var kbuf: [key_len]u8 = undefined;
        for (0..n) |i| try self.t.put(key(&kbuf, i), testValue(self.vbuf, vacLen(i), @truncate(i)));
        const order = try gpa.alloc(usize, n);
        defer gpa.free(order);
        for (order, 0..) |*o, i| o.* = i;
        var prng: std.Random.DefaultPrng = .init(n);
        prng.random().shuffle(usize, order);
        for (order) |i| if (!keep(i)) try std.testing.expect(try self.t.delete(key(&kbuf, i)));
        // Put the values with chains again. The new chains take pages from the free list, in any order.
        for (order) |i| if (keep(i) and vacLen(i) > max_local) try self.t.put(key(&kbuf, i), testValue(self.vbuf, vacLen(i), @truncate(i)));
    }

    /// Checks the tree, and that keys `0..n` are in it if `keep` accepts them.
    fn expect(self: *VacTest, n: usize, comptime keep: fn (usize) bool) !void {
        try self.t.check();
        var kbuf: [key_len]u8 = undefined;
        for (0..n) |i| {
            const got = try self.t.get(key(&kbuf, i), self.out);
            if (keep(i)) {
                try std.testing.expectEqualSlices(u8, testValue(self.vbuf, vacLen(i), @truncate(i)), got.?);
            } else try std.testing.expectEqual(null, got);
        }
    }
};

test "BPTree vacuum truncates the free tail" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    try t.put("a", "1");
    const small = t.npages;

    // Three values of 4 pages each. The chains take new pages at the end of the file, in order.
    for ("xyz", 0..) |c, i| try t.put(&.{c}, testValue(vt.vbuf, 4 * ovfl_cap, @intCast(i)));
    try std.testing.expectEqual(small + 12, t.npages);
    // The free list: the pages of "x", then the pages of "z".
    try std.testing.expect(try t.delete("z"));
    try std.testing.expect(try t.delete("x"));

    // The pages of "z" are at the end, so they go. The pages of "x" are before the pages of "y", so they stay.
    // The last page of "x" on the list gets a link of 0.
    const s = try t.vacuum(.truncate);
    try std.testing.expectEqual(BPTree.VacuumStats{ .before = small + 12, .after = small + 8, .moved = 0 }, s);
    try std.testing.expectEqual(@as(u64, t.npages) * page_size, try vt.fileLen());
    try std.testing.expectEqual(4, try vt.freePages());
    try t.check();
    // Nothing more is at the end.
    try std.testing.expectEqual(BPTree.VacuumStats{ .before = small + 8, .after = small + 8, .moved = 0 }, try t.vacuum(.truncate));

    // The file stays short when the tree is open again, and the new free list works.
    try vt.crash();
    try std.testing.expectEqual(small + 8, t.npages);
    try t.check();
    try std.testing.expectEqualSlices(u8, testValue(vt.vbuf, 4 * ovfl_cap, 1), (try t.get("y", vt.out)).?);
    try t.put("x", testValue(vt.vbuf, 4 * ovfl_cap, 0));
    try std.testing.expectEqual(small + 8, t.npages);
    try std.testing.expectEqual(0, try vt.freePages());
    try t.check();
}

/// The value length of key `i` in the vacuum tests: one value in five has a chain of up to three pages.
fn vacLen(i: usize) usize {
    return if (i % 5 == 0) max_local + 1 + i * 97 % (3 * ovfl_cap) else 10 + i % 40;
}

fn keepThird(i: usize) bool {
    return i % 3 == 0;
}

fn keepAll(_: usize) bool {
    return true;
}

test "BPTree vacuum moves pages to the free pages" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    const before = t.npages;
    const nfree = try vt.freePages();
    try std.testing.expect(nfree > before / 2);

    const s = try t.vacuum(.full);
    try std.testing.expectEqual(before, s.before);
    try std.testing.expectEqual(before - nfree, s.after);
    try std.testing.expect(s.moved > 0);
    // No free page is left, so check shows that each page below npages is in the tree.
    try std.testing.expectEqual(0, t.freelist);
    try std.testing.expectEqual(@as(u64, s.after) * page_size, try vt.fileLen());
    try vt.expect(N, keepThird);
    try std.testing.expectEqual(BPTree.VacuumStats{ .before = s.after, .after = s.after, .moved = 0 }, try t.vacuum(.full));

    try vt.crash();
    try std.testing.expectEqual(s.after, t.npages);
    try vt.expect(N, keepThird);
    // The tree grows again from the new end of the file.
    var kbuf: [VacTest.key_len]u8 = undefined;
    for (0..N) |i| if (!keepThird(i)) try t.put(VacTest.key(&kbuf, i), testValue(vt.vbuf, vacLen(i), @truncate(i)));
    try vt.expect(N, keepAll);
}

test "BPTree vacuum moves the root" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    const root = t.root;
    const s = try t.vacuum(.full);
    try std.testing.expect(root >= s.after);
    try std.testing.expect(t.root < s.after);
    try vt.expect(N, keepThird);
    try vt.crash();
    try vt.expect(N, keepThird);
}

test "BPTree incremental vacuum" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    const before = t.npages;
    const nfree = try vt.freePages();

    // Each step makes the file at least 7 pages shorter: more if the pages before the cut are free too.
    // The free pages below the new end stay on the free list.
    var s = try t.vacuum(.{ .incremental = 7 });
    try std.testing.expect(s.after <= before - 7);
    try std.testing.expectEqual(nfree - (before - s.after), try vt.freePages());
    try vt.expect(N, keepThird);
    const first = s.after;
    s = try t.vacuum(.{ .incremental = 7 });
    try std.testing.expect(s.after <= first - 7);
    try std.testing.expectEqual(nfree - (before - s.after), try vt.freePages());
    try std.testing.expectEqual(@as(u64, s.after) * page_size, try vt.fileLen());
    try vt.expect(N, keepThird);

    // A step larger than the free list frees all of it.
    s = try t.vacuum(.{ .incremental = before });
    try std.testing.expectEqual(before - nfree, s.after);
    try std.testing.expectEqual(0, try vt.freePages());
    try vt.expect(N, keepThird);
}

test "BPTree vacuum crash after the moves" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    try t.sync();
    const before = t.npages;
    const nfree = try vt.freePages();
    const root = t.root;

    // The crash comes after all the moves, before `shrink`. The pool loses the moved pages.
    const free = try VacTest.gpa.alloc(bool, before);
    defer VacTest.gpa.free(free);
    const list = try VacTest.gpa.alloc(u32, before);
    defer VacTest.gpa.free(list);
    _ = try t.markFree(free, list);
    try std.testing.expect(try t.moveTail(free, before) > 0);
    const new_root = t.root;
    try std.testing.expect(new_root != root);
    try vt.crash();

    // Recovery does the moves again from the log. The file is as long as before, and the old pages are free.
    try std.testing.expectEqual(new_root, t.root);
    try std.testing.expectEqual(before, t.npages);
    try std.testing.expectEqual(nfree, try vt.freePages());
    try vt.expect(N, keepThird);
    // A vacuum after the crash does the work again.
    try std.testing.expectEqual(before - nfree, (try t.vacuum(.full)).after);
    try vt.expect(N, keepThird);
}

test "BPTree vacuum crash after the new free list is in the file" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    try t.put("a", "1");
    for ("wxyz", 0..) |c, i| try t.put(&.{c}, testValue(vt.vbuf, 4 * ovfl_cap, @intCast(i)));
    // The free list: the pages of "w", then "x", then "z". "z" is at the end of the file.
    _ = try t.delete("z");
    _ = try t.delete("x");
    _ = try t.delete("w");
    try t.sync();
    const npages = t.npages;

    // The pages of "z" come off the list, so the last page of "x" on the list gets a link of 0.
    const free = try VacTest.gpa.alloc(bool, npages);
    defer VacTest.gpa.free(free);
    const list = try VacTest.gpa.alloc(u32, npages);
    defer VacTest.gpa.free(list);
    const nfree = try t.markFree(free, list);
    try std.testing.expectEqual(12, nfree);
    t.durable = false;
    try t.relinkFree(free, list[0..nfree], npages - 4);
    const changed = list[7];
    const p = try t.getPage(changed);
    try std.testing.expectEqual(0, p.link());
    t.pool.unpin(p, .clean);
    // The changed page waits for the log record, so an eviction of it makes the record durable first.
    // (A paranoid pool writes a page out at each unpin, so there the record is durable already.)
    if (!build_options.pool_paranoid) {
        try std.testing.expect(t.pool.wal.end.raw > t.pool.wal.durable.raw);
        try std.testing.expectEqual(t.pool.wal.end.raw, t.pool.frames[t.pool.find(changed).?].lsn.raw);
    }

    // The new link reaches the file, and the crash comes before the meta page.
    try t.pool.wal.flushTo(VacTest.io, t.pool.wal.end.raw);
    try t.pool.flush();
    try vt.crash();

    // The meta page still points to the old list, which now ends before the pages of "z".
    // Recovery sees the log record and builds the free list again.
    try std.testing.expectEqual(npages, t.npages);
    try std.testing.expectEqual(12, try vt.freePages());
    try t.check();
    try std.testing.expectEqualSlices(u8, testValue(vt.vbuf, 4 * ovfl_cap, 2), (try t.get("y", vt.out)).?);
}

test "BPTree vacuum crash before the file is cut" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    const before = t.npages;

    // The crash comes after the meta page with the new npages, before the file is cut.
    const free = try VacTest.gpa.alloc(bool, before);
    defer VacTest.gpa.free(free);
    const list = try VacTest.gpa.alloc(u32, before);
    defer VacTest.gpa.free(list);
    const nfree = try t.markFree(free, list);
    _ = try t.moveTail(free, before);
    try t.shrink(free, list[0..nfree]);
    const after = t.npages;
    try std.testing.expect(after < before);
    try vt.crash();

    // The tree uses only the first `after` pages. The rest of the file stays until the next vacuum.
    try std.testing.expectEqual(after, t.npages);
    try std.testing.expect(try vt.fileLen() > @as(u64, after) * page_size);
    try vt.expect(N, keepThird);
    try std.testing.expectEqual(BPTree.VacuumStats{ .before = after, .after = after, .moved = 0 }, try t.vacuum(.truncate));
    try std.testing.expectEqual(@as(u64, after) * page_size, try vt.fileLen());
    try vt.expect(N, keepThird);
}

test "BPTree vacuum pages wait for their log records" {
    if (build_options.pool_paranoid) return error.SkipZigTest;
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    try t.sync();
    t.durable = false;

    // The pages of a move carry the LSN of its commit, so an eviction makes the commit durable first.
    const owners = try VacTest.gpa.alloc(BPTree.Owner, t.npages);
    defer VacTest.gpa.free(owners);
    @memset(owners, .{});
    var last_leaf: u32 = 0;
    try t.markOwners(owners, t.root, .{ .kind = .root }, &last_leaf, 0);
    var from = t.npages - 1;
    while (owners[from].kind != .child) from -= 1;
    const o = owners[from];
    var to: u32 = 1;
    while (owners[to].kind != .free) to += 1;
    try t.movePage(owners, from, to);
    try std.testing.expect(t.pool.wal.end.raw > t.pool.wal.durable.raw);
    for ([_]u32{ to, o.from }) |pg| try std.testing.expectEqual(t.pool.wal.end.raw, t.pool.frames[t.pool.find(pg).?].lsn.raw);
    // Page `to` is still on the free list, so only recovery can make the tree whole again.
    try vt.crash();
    try vt.expect(N, keepThird);
}

test "BPTree vacuum and sync wait for the operations that run" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    try vt.fill(300, keepThird);
    const before = t.npages;

    const V = struct {
        fn vacuum(tree: *BPTree, d: *std.atomic.Value(bool)) void {
            _ = tree.vacuum(.full) catch |err| std.debug.panic("vacuum: {t}", .{err});
            d.store(true, .release);
        }
        fn sync(tree: *BPTree, d: *std.atomic.Value(bool)) void {
            tree.sync() catch |err| std.debug.panic("sync: {t}", .{err});
            d.store(true, .release);
        }
    };
    inline for (.{ V.vacuum, V.sync }) |f| {
        // Hold the gate as an operation does. The other thread must wait until the operation ends.
        const n = t.npages;
        t.gate.lockSharedUncancelable(VacTest.io);
        var done: std.atomic.Value(bool) = .init(false);
        const th = try std.Thread.spawn(.{}, f, .{ t, &done });
        try VacTest.io.sleep(.fromMilliseconds(50), .awake);
        try std.testing.expect(!done.load(.acquire));
        try std.testing.expectEqual(n, @atomicLoad(u32, &t.npages, .monotonic));
        t.gate.unlockShared(VacTest.io);
        th.join();
        try std.testing.expect(done.load(.acquire));
    }
    try std.testing.expect(t.npages < before);
    try vt.expect(300, keepThird);
}

/// Puts, deletes, gets and scans the keys `first..first + n`, and checks each result. It is one thread of the next test.
const VacWriter = struct {
    t: *BPTree,
    first: usize,
    n: usize,
    /// Which of the keys are in the tree.
    present: []bool,
    done: std.atomic.Value(bool) = .init(false),
    err: ?anyerror = null,

    fn go(w: *VacWriter) void {
        w.loop() catch |err| {
            w.err = err;
        };
        w.done.store(true, .release);
    }

    fn loop(w: *VacWriter) !void {
        const vbuf = try VacTest.gpa.alloc(u8, 4 * ovfl_cap);
        defer VacTest.gpa.free(vbuf);
        const out = try VacTest.gpa.alloc(u8, 4 * ovfl_cap);
        defer VacTest.gpa.free(out);
        var kbuf: [VacTest.key_len]u8 = undefined;
        var prng: std.Random.DefaultPrng = .init(w.first);
        const rand = prng.random();
        for (0..2000) |_| {
            const j = rand.uintLessThan(usize, w.n);
            const what = rand.uintLessThan(usize, 4);
            // An operation that finds the pool full changes nothing, so it can run again.
            while (true) break w.step(what, j, &kbuf, vbuf, out) catch |err| {
                if (err != error.PoolExhausted) return err;
                std.Thread.yield() catch {};
                continue;
            };
        }
    }

    fn step(w: *VacWriter, what: usize, j: usize, kbuf: *[VacTest.key_len]u8, vbuf: []u8, out: []u8) !void {
        const i = w.first + j;
        const key = VacTest.key(kbuf, i);
        const val = testValue(vbuf, vacLen(i), @truncate(i));
        switch (what) {
            0 => {
                try w.t.put(key, val);
                w.present[j] = true;
            },
            1 => {
                try std.testing.expectEqual(w.present[j], try w.t.delete(key));
                w.present[j] = false;
            },
            2 => {
                const got = try w.t.get(key, out);
                if (w.present[j]) {
                    try std.testing.expectEqualSlices(u8, val, got.?);
                } else try std.testing.expectEqual(null, got);
            },
            else => {
                // Only this thread writes these keys, so the scan must give exactly the keys that are present.
                var lo: [VacTest.key_len]u8 = undefined;
                var hi: [VacTest.key_len]u8 = undefined;
                var c: ScanCount = .{ .vbuf = vbuf };
                const n = try w.t.scan(VacTest.key(&lo, w.first), VacTest.key(&hi, w.first + w.n), &c, ScanCount.visit);
                try std.testing.expectEqual(std.mem.count(bool, w.present, &.{true}), n);
                if (c.bad) return error.TestUnexpectedResult;
            },
        }
    }

    const ScanCount = struct {
        vbuf: []u8,
        bad: bool = false,

        fn visit(c: *ScanCount, k: []const u8, v: []const u8) anyerror!void {
            const i = std.fmt.parseInt(usize, k[0..8], 10) catch return error.TestUnexpectedResult;
            if (!std.mem.eql(u8, testValue(c.vbuf, vacLen(i), @truncate(i)), v)) c.bad = true;
        }
    };
};

test "BPTree online vacuum stops at its goal" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);
    const before = t.npages;

    // The step is larger than the goal, so one step of 7 pages does it, and it moves at most 7 pages.
    const s = try t.vacuumOnline(.{ .incremental = 7 }, 64, 100);
    try std.testing.expect(s.after <= before - 7);
    try std.testing.expect(s.moved <= 7);
    try vt.expect(N, keepThird);
}

test "BPTree vacuum while other threads use the tree" {
    var vt: VacTest = undefined;
    try vt.init();
    defer vt.deinit();
    const t = &vt.t;
    const N = 600;
    try vt.fill(N, keepThird);

    // Three threads write keys after N, and the main thread vacuums in steps until they end.
    var ws: [3]VacWriter = undefined;
    var present: [3][100]bool = @splat(@splat(false));
    var ths: [3]std.Thread = undefined;
    for (&ws, &present, &ths, 0..) |*w, *pr, *th, i| {
        w.* = .{ .t = t, .first = N + i * 100, .n = 100, .present = pr };
        th.* = try std.Thread.spawn(.{}, VacWriter.go, .{w});
    }
    var steps: usize = 0;
    var running = true;
    while (running) {
        _ = t.vacuumOnline(.full, 8, 50) catch |err| if (err != error.PoolExhausted) return err;
        steps += 1;
        running = false;
        for (&ws) |*w| running = running or !w.done.load(.acquire);
    }
    for (&ths) |th| th.join();
    for (&ws) |*w| if (w.err) |err| return err;
    try std.testing.expect(steps > 1);

    try vt.expect(N, keepThird);
    var kbuf: [VacTest.key_len]u8 = undefined;
    for (&ws) |*w| for (w.present, 0..) |p, j| {
        const got = try t.get(VacTest.key(&kbuf, w.first + j), vt.out);
        try std.testing.expectEqual(p, got != null);
    };
    _ = try t.vacuum(.full);
    try std.testing.expectEqual(0, t.freelist);
    try t.check();
    try vt.crash();
    try vt.expect(N, keepThird);
}
