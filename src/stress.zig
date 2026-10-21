//! A stress test and a benchmark for the tree.
//!
//!   stress test [threads] [ops per thread] [rounds]
//!   stress bench [threads] [read percent] [ops per thread]
const std = @import("std");
const Io = std.Io;
const bpt = @import("bplustree_zig");

/// The keys of the test are key00000000 to key00019999. Thread `id` writes only the keys with `k % threads == id`.
const test_keys = 20000;
/// The benchmark loads this many keys first.
const bench_keys = 50000;
/// A run that takes longer than this has hung.
const timeout_s = 600;

fn keyOf(buf: *[16]u8, k: usize) []const u8 {
    return std.fmt.bufPrint(buf, "key{d:0>8}", .{k}) catch unreachable;
}

/// The length of version `ver` of the value of key `k`: from 8 bytes up to `max_val`.
fn valLen(k: usize, ver: u32) usize {
    return 8 + (k *% 7919 +% @as(usize, ver) *% 104729) % (bpt.max_val - 8 + 1);
}

/// A value says which key and version it belongs to, and then repeats one byte that depends on both.
/// A reader can check any value it gets, so it notices a value torn by a writer.
fn makeVal(buf: *[bpt.max_val]u8, k: usize, ver: u32) []const u8 {
    const v = buf[0..valLen(k, ver)];
    std.mem.writeInt(u32, v[0..4], @intCast(k), .little);
    std.mem.writeInt(u32, v[4..8], ver, .little);
    @memset(v[8..], @truncate(k ^ ver *% 31));
    return v;
}

/// The version in `v` if it is a whole value of key `k`, or null.
fn valVersion(v: []const u8, k: usize) ?u32 {
    if (v.len < 8 or std.mem.readInt(u32, v[0..4], .little) != k) return null;
    const ver = std.mem.readInt(u32, v[4..8], .little);
    if (v.len != valLen(k, ver)) return null;
    for (v[8..]) |b| if (b != @as(u8, @truncate(k ^ ver *% 31))) return null;
    return ver;
}

fn fail(comptime fmt: []const u8, args: anytype) noreturn {
    std.debug.panic("stress: " ++ fmt, args);
}

/// The number `k` in a key that `keyOf` made, or null.
fn keyNum(key: []const u8) ?usize {
    if (key.len != 11 or !std.mem.startsWith(u8, key, "key")) return null;
    return std.fmt.parseInt(usize, key[3..], 10) catch null;
}

const Shared = struct {
    t: *bpt.BPTree,
    threads: usize,
    ops: usize,
    read_pct: usize = 50,
    /// The version of each key that its writer last put, or 0 if the key is not in the tree.
    /// Only the writer of a key touches its entry while the threads run.
    vers: []u32 = &.{},
    /// Operations that failed with error.PoolExhausted and ran again.
    retries: std.atomic.Value(u64) = .init(0),

    /// An operation that fails with error.PoolExhausted changes nothing, so it can run again.
    fn again(sh: *Shared, err: anyerror) !void {
        if (err != error.PoolExhausted) return err;
        _ = sh.retries.fetchAdd(1, .monotonic);
        std.Thread.yield() catch {};
    }
};

/// Checks one scan of the keys `lo..hi`. The keys must come in order and inside the bounds, and each value must be whole.
/// The keys that thread `id` writes must be exactly the ones it put, with their last versions.
/// If `id` is null, no thread runs, so all keys must be exactly as the writers put them.
const ScanCheck = struct {
    sh: *Shared,
    id: ?usize,
    lo: usize,
    hi: usize,
    /// The smallest key that the scan can give next.
    next: usize,
    n: usize = 0,

    fn owns(c: *const ScanCheck, k: usize) bool {
        return if (c.id) |id| k % c.sh.threads == id else true;
    }

    fn visit(c: *ScanCheck, key: []const u8, val: []const u8) anyerror!void {
        const k = keyNum(key) orelse fail("scan {d}..{d}: bad key {s}", .{ c.lo, c.hi, key });
        if (k < c.next or k > c.hi) fail("scan {d}..{d}: key {d} after key {d}", .{ c.lo, c.hi, k, c.next -| 1 });
        c.missing(k);
        const ver = valVersion(val, k) orelse fail("scan {d}..{d}: key {d} has a torn or wrong value", .{ c.lo, c.hi, k });
        if (c.owns(k) and ver != c.sh.vers[k]) fail("scan {d}..{d}: key {d} has version {d}, put {d}", .{ c.lo, c.hi, k, ver, c.sh.vers[k] });
        c.next = k + 1;
        c.n += 1;
    }

    /// Fails if the scan skipped a key before `end` that it must give.
    fn missing(c: *const ScanCheck, end: usize) void {
        for (c.next..end) |k| {
            if (c.owns(k) and c.sh.vers[k] != 0) fail("scan {d}..{d}: key {d} is missing", .{ c.lo, c.hi, k });
        }
    }
};

fn testWorker(sh: *Shared, id: usize, seed: u64) !void {
    const t = sh.t;
    var prng: std.Random.DefaultPrng = .init(seed);
    const rand = prng.random();
    var kbuf: [16]u8 = undefined;
    var vbuf: [bpt.max_val]u8 = undefined;
    var out: [bpt.max_val]u8 = undefined;
    const owned = (test_keys - id + sh.threads - 1) / sh.threads;

    for (0..sh.ops) |_| {
        const roll = rand.uintLessThan(usize, 100);
        if (roll < 40) {
            // Get any key. A key that another thread writes can have any version, but it must be whole.
            const k = rand.uintLessThan(usize, test_keys);
            const got = while (true) break t.get(keyOf(&kbuf, k), &out) catch |err| {
                try sh.again(err);
                continue;
            };
            if (got) |v| {
                const ver = valVersion(v, k) orelse fail("get {d}: a torn or wrong value", .{k});
                if (k % sh.threads == id and ver != sh.vers[k]) fail("get {d}: version {d}, put {d}", .{ k, ver, sh.vers[k] });
            } else if (k % sh.threads == id and sh.vers[k] != 0) fail("get {d}: missing", .{k});
            continue;
        }
        if (roll < 50) {
            // Scan a range of up to 256 keys, while the other threads write into it.
            const lo = rand.uintLessThan(usize, test_keys);
            const hi = @min(test_keys - 1, lo + rand.uintLessThan(usize, 256));
            var lbuf: [16]u8 = undefined;
            var hbuf: [16]u8 = undefined;
            var c: ScanCheck = undefined;
            const n = while (true) {
                // A scan that fails part of the way can visit keys before it fails, so start the check again.
                c = .{ .sh = sh, .id = id, .lo = lo, .hi = hi, .next = lo };
                break t.scan(keyOf(&lbuf, lo), keyOf(&hbuf, hi), &c, ScanCheck.visit) catch |err| {
                    try sh.again(err);
                    continue;
                };
            };
            c.missing(hi + 1);
            if (n != c.n) fail("scan {d}..{d}: gives {d} keys, but visited {d}", .{ lo, hi, n, c.n });
            continue;
        }

        const k = id + sh.threads * rand.uintLessThan(usize, owned);
        if (roll < 80) {
            const ver = rand.int(u32) | 1;
            while (true) break t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, ver)) catch |err| {
                try sh.again(err);
                continue;
            };
            sh.vers[k] = ver;
        } else {
            const found = while (true) break t.delete(keyOf(&kbuf, k)) catch |err| {
                try sh.again(err);
                continue;
            };
            if (found != (sh.vers[k] != 0)) fail("delete {d}: found is {}", .{ k, found });
            sh.vers[k] = 0;
        }
    }
}

fn benchWorker(sh: *Shared, id: usize, seed: u64) !void {
    _ = id;
    const t = sh.t;
    var prng: std.Random.DefaultPrng = .init(seed);
    const rand = prng.random();
    var kbuf: [16]u8 = undefined;
    var vbuf: [bpt.max_val]u8 = undefined;
    var out: [bpt.max_val]u8 = undefined;
    @memset(&vbuf, 'v');

    for (0..sh.ops) |_| {
        const k = keyOf(&kbuf, rand.uintLessThan(usize, bench_keys));
        if (rand.uintLessThan(usize, 100) < sh.read_pct) {
            _ = while (true) break t.get(k, &out) catch |err| {
                try sh.again(err);
                continue;
            };
        } else {
            while (true) break t.put(k, vbuf[0..50]) catch |err| {
                try sh.again(err);
                continue;
            };
        }
    }
}

fn run(comptime worker: anytype, sh: *Shared, seed: u64) !void {
    var threads: [256]std.Thread = undefined;
    var errs: [256]?anyerror = @splat(null);
    const W = struct {
        fn go(s: *Shared, id: usize, sd: u64, err: *?anyerror) void {
            worker(s, id, sd) catch |e| {
                err.* = e;
            };
        }
    };
    for (threads[0..sh.threads], 0..) |*th, i| th.* = try std.Thread.spawn(.{}, W.go, .{ sh, i, seed + i, &errs[i] });
    for (threads[0..sh.threads]) |th| th.join();
    for (errs[0..sh.threads]) |e| if (e) |err| return err;
}

/// Ends the process if the run takes longer than `timeout_s`: an operation is waiting for a lock that is never released.
fn watchdog(io: Io, done: *std.atomic.Value(bool)) void {
    const start = Io.Clock.Timestamp.now(io, .awake);
    while (!done.load(.acquire)) {
        io.sleep(.fromMilliseconds(100), .awake) catch {};
        if (start.untilNow(io).raw.toSeconds() >= timeout_s) {
            std.debug.print("stress: timed out after {d} s, probably a deadlock\n", .{timeout_s});
            std.process.exit(3);
        }
    }
}

/// A tree's file and its log, which is the same path with `.wal` added.
const Files = struct {
    file: Io.File,
    log: Io.File,

    fn open(io: Io, path: []const u8, truncate: bool) !Files {
        var buf: [256]u8 = undefined;
        const log_path = try std.fmt.bufPrint(&buf, "{s}.wal", .{path});
        const file = try Io.Dir.cwd().createFile(io, path, .{ .read = true, .truncate = truncate });
        errdefer file.close(io);
        const log = try Io.Dir.cwd().createFile(io, log_path, .{ .read = true, .truncate = truncate });
        return .{ .file = file, .log = log };
    }

    fn close(f: Files, io: Io) void {
        f.file.close(io);
        f.log.close(io);
    }

    fn delete(io: Io, path: []const u8) void {
        var buf: [256]u8 = undefined;
        Io.Dir.cwd().deleteFile(io, path) catch {};
        Io.Dir.cwd().deleteFile(io, std.fmt.bufPrint(&buf, "{s}.wal", .{path}) catch return) catch {};
    }
};

/// Writes to keys `k % crash_threads == id` until the process ends.
fn crashWorker(t: *bpt.BPTree, id: usize, seed: u64) void {
    var prng: std.Random.DefaultPrng = .init(seed);
    const rand = prng.random();
    var kbuf: [16]u8 = undefined;
    var vbuf: [bpt.max_val]u8 = undefined;
    while (true) {
        const k = id + crash_threads * rand.uintLessThan(usize, test_keys / crash_threads);
        const key = keyOf(&kbuf, k);
        const r = if (rand.uintLessThan(usize, 10) < 7)
            t.put(key, makeVal(&vbuf, k, rand.int(u32) | 1))
        else if (t.delete(key)) |_| {} else |err| err;
        r catch |err| if (err != error.PoolExhausted) std.debug.panic("crash: {t}", .{err});
    }
}

const crash_threads = 4;

/// Fills a new tree in `path`, syncs it, and then writes from `crash_threads` threads
/// until the process ends after `ms` milliseconds, in the middle of their operations.
fn crash(io: Io, gpa: std.mem.Allocator, path: []const u8, seed: u64, ms: u64) !void {
    const f: Files = try .open(io, path, true);
    var t: bpt.BPTree = try .init(gpa, io, f.file, f.log);
    var kbuf: [16]u8 = undefined;
    var vbuf: [bpt.max_val]u8 = undefined;
    t.durable = false;
    for (0..test_keys) |k| try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, 1));
    try t.sync();
    t.durable = true;
    for (0..crash_threads) |id| _ = try std.Thread.spawn(.{}, crashWorker, .{ &t, id, seed + id });
    try io.sleep(.fromMilliseconds(@intCast(ms)), .awake);
    // Like a crash of the process: no sync, no deinit, and the threads stop wherever they are.
    std.process.exit(0);
}

/// Opens the tree in `path` and checks it: the tree must be whole, and every value must be a whole value of its key.
fn verify(io: Io, gpa: std.mem.Allocator, path: []const u8) !void {
    const f: Files = try .open(io, path, false);
    defer f.close(io);
    var t: bpt.BPTree = try .init(gpa, io, f.file, f.log);
    defer t.deinit(gpa);
    try t.check(gpa);
    const V = struct {
        fn visit(_: void, key: []const u8, val: []const u8) !void {
            const k = keyNum(key) orelse return error.BadKey;
            if (valVersion(val, k) == null) return error.BadValue;
        }
    };
    const n = try t.scan(null, null, {}, V.visit);
    std.debug.print("verify: ok, {d} keys\n", .{n});
}
fn arg(args: []const [:0]const u8, i: usize, default: usize) !usize {
    return if (args.len > i) try std.fmt.parseInt(usize, args[i], 10) else default;
}

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const gpa = init.gpa;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    const mode = if (args.len > 1) args[1] else "test";

    if (std.mem.eql(u8, mode, "crash") and args.len > 4)
        return crash(io, gpa, args[2], try arg(args, 3, 1), try arg(args, 4, 100));
    if (std.mem.eql(u8, mode, "verify") and args.len > 2) return verify(io, gpa, args[2]);

    var rnd: [4]u8 = undefined;
    io.random(&rnd);
    var name_buf: [32]u8 = undefined;
    const name = try std.fmt.bufPrint(&name_buf, "stress-{x}.bin", .{std.mem.readInt(u32, &rnd, .little)});
    const f: Files = try .open(io, name, true);
    defer {
        f.close(io);
        Files.delete(io, name);
    }
    var t: bpt.BPTree = try .init(gpa, io, f.file, f.log);
    defer t.deinit(gpa);

    var done: std.atomic.Value(bool) = .init(false);
    const dog = try std.Thread.spawn(.{}, watchdog, .{ io, &done });
    defer {
        done.store(true, .release);
        dog.join();
    }

    if (std.mem.eql(u8, mode, "test")) {
        var sh: Shared = .{ .t = &t, .threads = try arg(args, 2, 8), .ops = try arg(args, 3, 20000) };
        const rounds = try arg(args, 4, 5);
        sh.vers = try gpa.alloc(u32, test_keys);
        defer gpa.free(sh.vers);
        @memset(sh.vers, 0);

        var kbuf: [16]u8 = undefined;
        var vbuf: [bpt.max_val]u8 = undefined;
        var out: [bpt.max_val]u8 = undefined;
        for (0..rounds) |round| {
            try run(testWorker, &sh, 1 + round * 1000);
            // Every thread has stopped, so the tree must be whole and hold exactly what the writers put.
            try t.check(gpa);
            var present: usize = 0;
            for (sh.vers, 0..) |ver, k| {
                const got = try t.get(keyOf(&kbuf, k), &out);
                if (ver == 0) {
                    if (got != null) fail("key {d} is in the tree after its delete", .{k});
                } else {
                    if (got == null or !std.mem.eql(u8, got.?, makeVal(&vbuf, k, ver))) fail("key {d} has the wrong value", .{k});
                    present += 1;
                }
            }
            var c: ScanCheck = .{ .sh = &sh, .id = null, .lo = 0, .hi = test_keys - 1, .next = 0 };
            const n = try t.scan(null, null, &c, ScanCheck.visit);
            c.missing(test_keys);
            if (n != present) fail("scan of all keys gives {d} keys, but {d} are in the tree", .{ n, present });
            try t.sync();
            std.debug.print("round {d}: ok, {d} keys\n", .{ round, present });
        }
        std.debug.print("stress test passed: {d} threads, {d} ops each, {d} rounds, {d} retries\n", .{ sh.threads, sh.ops, rounds, sh.retries.raw });
    } else if (std.mem.eql(u8, mode, "bench")) {
        var sh: Shared = .{ .t = &t, .threads = try arg(args, 2, 4), .read_pct = try arg(args, 3, 90), .ops = try arg(args, 4, 50000) };
        var kbuf: [16]u8 = undefined;
        const val: [50]u8 = @splat('v');
        // Load without waiting for the log after every put. The sync at the end makes it all durable.
        t.durable = false;
        for (0..bench_keys) |k| try t.put(keyOf(&kbuf, k), &val);
        try t.sync();
        t.durable = args.len <= 5 or !std.mem.eql(u8, args[5], "nosync");

        const syncs = t.pool.wal.syncs.raw;
        const locks = t.pool.locks;
        const start = Io.Clock.Timestamp.now(io, .awake);
        try run(benchWorker, &sh, 7);
        const ns: u64 = @intCast(start.untilNow(io).raw.toNanoseconds());
        const total = sh.threads * sh.ops;
        std.debug.print("threads={d} reads={d}% ops={d} time_ms={d} ops_per_s={d} retries={d} log_syncs={d} pool_locks_per_op={d:.2}\n", .{
            sh.threads,                     sh.read_pct,    total,                        ns / std.time.ns_per_ms,
            total * std.time.ns_per_s / ns, sh.retries.raw, t.pool.wal.syncs.raw - syncs, @as(f64, @floatFromInt(t.pool.locks - locks)) / @as(f64, @floatFromInt(total)),
        });
    } else {
        std.debug.print("usage: stress test [threads] [ops] [rounds] | stress bench [threads] [read%] [ops]" ++
            " | stress crash <file> <seed> <ms> | stress verify <file>\n", .{});
        return error.BadArgs;
    }
}
