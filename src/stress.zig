//! A stress test and a benchmark for the tree.
//!
//!   stress test [threads] [ops per thread] [rounds]
//!   stress bench [threads] [read percent] [ops per thread]
//!   stress scanmix [scan percent] [update percent] [ops] [nosync]
//!   stress shrink [keep percent] [truncate | full | pages]
//!   stress vaccrash <file> <seed> <ms>
//!   stress online [threads] [step] [busy percent] [read percent]
//!   stress onlinecrash <file> <seed> <ms>
const std = @import("std");
const Io = std.Io;
const bpt = @import("bplustree_zig");

/// The keys of the test are key00000000 to key00019999. Thread `id` writes only the keys with `k % threads == id`.
const test_keys = 20000;
/// The benchmark loads this many keys first.
const bench_keys = 50000;
/// The hot keys of `scanmix`: `hot_runs` runs of `hot_len` keys, spread over the keys of the benchmark.
const hot_runs = 4;
const hot_len = 16;
/// The number of keys in one scan of `scanmix`.
const scan_len = 1000;
/// The longest value of the test: three pages, so that its chain has up to three overflow pages.
const max_test_val = 24 * bpt.max_local;
/// A run that takes longer than this has hung.
const timeout_s = 600;

fn keyOf(buf: *[16]u8, k: usize) []const u8 {
    return std.fmt.bufPrint(buf, "key{d:0>8}", .{k}) catch unreachable;
}

/// The length of version `ver` of the value of key `k`: from 8 bytes up to `bpt.max_local`,
/// or for one version in four, up to `max_test_val`, so that most of those have a chain.
fn valLen(k: usize, ver: u32) usize {
    const h = k *% 7919 +% @as(usize, ver) *% 104729;
    const max: usize = if (h % 4 == 0) max_test_val else bpt.max_local;
    return 8 + (h / 4) % (max - 8 + 1);
}

/// A value says which key and version it belongs to, and then repeats one byte that depends on both.
/// A reader can check any value it gets, so it notices a value torn by a writer.
fn makeVal(buf: *[max_test_val]u8, k: usize, ver: u32) []const u8 {
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
    /// `onlineWorker` stops when this is true.
    stop: std.atomic.Value(bool) = .init(false),
    /// The latencies of `onlineWorker`, one for each thread.
    lats: []Lat = &.{},

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
    var vbuf: [max_test_val]u8 = undefined;
    var out: [max_test_val]u8 = undefined;
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
                break t.scan(keyOf(&lbuf, lo), keyOf(&hbuf, hi + 1), &c, ScanCheck.visit) catch |err| {
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
    var vbuf: [max_test_val]u8 = undefined;
    var out: [max_test_val]u8 = undefined;
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

/// The latencies of operations. Bucket `i` counts the operations that took less than 2^i microseconds.
const Lat = struct {
    buckets: [32]u64 = @splat(0),
    n: u64 = 0,
    max_ns: u64 = 0,

    fn add(l: *Lat, ns: u64) void {
        l.n += 1;
        l.max_ns = @max(l.max_ns, ns);
        l.buckets[@min(31, std.math.log2_int_ceil(u64, ns / std.time.ns_per_us + 1))] += 1;
    }

    fn merge(l: *Lat, o: Lat) void {
        for (&l.buckets, o.buckets) |*b, x| b.* += x;
        l.n += o.n;
        l.max_ns = @max(l.max_ns, o.max_ns);
    }

    /// An upper bound, in microseconds, of the latency that a fraction `q` of the operations do not pass.
    fn quantile(l: *const Lat, q: f64) u64 {
        const want: u64 = @intFromFloat(@ceil(q * @as(f64, @floatFromInt(l.n))));
        var seen: u64 = 0;
        for (l.buckets, 0..) |b, i| {
            seen += b;
            if (seen >= want) return @as(u64, 1) << @intCast(i);
        }
        return std.math.maxInt(u64);
    }
};

/// Gets and puts any key until `sh.stop` is true, and records the latency of each operation.
/// A put gives the key a new version of its value, so a value with a chain frees the old chain.
fn onlineWorker(sh: *Shared, id: usize, seed: u64) !void {
    const t = sh.t;
    const io = t.pool.io;
    var prng: std.Random.DefaultPrng = .init(seed);
    const rand = prng.random();
    var kbuf: [16]u8 = undefined;
    var vbuf: [max_test_val]u8 = undefined;
    var out: [max_test_val]u8 = undefined;
    const lat = &sh.lats[id];

    while (!sh.stop.load(.acquire)) {
        const k = rand.uintLessThan(usize, bench_keys);
        const key = keyOf(&kbuf, k);
        const start = Io.Clock.Timestamp.now(io, .awake);
        if (rand.uintLessThan(usize, 100) < sh.read_pct) {
            _ = while (true) break t.get(key, &out) catch |err| {
                try sh.again(err);
                continue;
            };
        } else {
            while (true) break t.put(key, makeVal(&vbuf, k, rand.int(u32) | 1)) catch |err| {
                try sh.again(err);
                continue;
            };
        }
        lat.add(@intCast(start.untilNow(io).raw.toNanoseconds()));
    }
}

/// Starts a thread that runs `worker` in the threads of `sh`. The thread ends when the workers see `sh.stop`.
fn runInBackground(comptime worker: anytype, sh: *Shared, seed: u64) !std.Thread {
    sh.stop.store(false, .release);
    return std.Thread.spawn(.{}, struct {
        fn go(s: *Shared, sd: u64) void {
            run(worker, s, sd) catch |err| std.debug.panic("stress: {t}", .{err});
        }
    }.go, .{ sh, seed });
}

fn printLat(what: []const u8, sh: *const Shared, ns: u64) void {
    var all: Lat = .{};
    for (sh.lats) |l| all.merge(l);
    std.debug.print("{s}: ops={d} ops_per_s={d} p50_us<{d} p99_us<{d} p999_us<{d} max_ms={d}\n", .{
        what, all.n, all.n * std.time.ns_per_s / ns, all.quantile(0.5), all.quantile(0.99), all.quantile(0.999), all.max_ns / std.time.ns_per_ms,
    });
}

/// Loads `bench_keys` keys and deletes 3 of 4, as `shrink` does. Then `threads` threads get and put keys:
/// first for 5 seconds without a vacuum, then while the main thread vacuums in steps of `step` pages,
/// with a rest after each step so that the steps take at most `busy_pct` percent of the time.
/// It prints the latencies of the operations in both parts, and how long each step held them out.
fn online(t: *bpt.BPTree, io: Io, gpa: std.mem.Allocator, sh: *Shared, step: u32, busy_pct: u32) !void {
    var kbuf: [16]u8 = undefined;
    var vbuf: [max_test_val]u8 = undefined;
    t.durable = false;
    for (0..bench_keys) |k| try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, 1));
    var prng: std.Random.DefaultPrng = .init(11);
    const rand = prng.random();
    for (0..bench_keys) |k| {
        if (rand.uintLessThan(usize, 100) >= 25) _ = try t.delete(keyOf(&kbuf, k));
    }
    try t.sync();
    t.durable = true;
    sh.lats = try gpa.alloc(Lat, sh.threads);
    defer gpa.free(sh.lats);

    @memset(sh.lats, .{});
    var start = Io.Clock.Timestamp.now(io, .awake);
    var th = try runInBackground(onlineWorker, sh, 5);
    try io.sleep(.fromSeconds(5), .awake);
    sh.stop.store(true, .release);
    th.join();
    printLat("no vacuum", sh, @intCast(start.untilNow(io).raw.toNanoseconds()));

    // The same steps as `vacuumOnline`, but each step is timed here.
    @memset(sh.lats, .{});
    var steps: Lat = .{};
    var moved: u64 = 0;
    const before = t.npages;
    start = Io.Clock.Timestamp.now(io, .awake);
    th = try runInBackground(onlineWorker, sh, 6);
    while (true) {
        const s0 = Io.Clock.Timestamp.now(io, .awake);
        const s = try t.vacuum(.{ .incremental = step });
        steps.add(@intCast(s0.untilNow(io).raw.toNanoseconds()));
        moved += s.moved;
        if (s.after == s.before) break;
        const sns: u64 = @intCast(s0.untilNow(io).raw.toNanoseconds());
        try io.sleep(.fromNanoseconds(@max(std.time.ns_per_ms, sns * (100 - busy_pct) / busy_pct)), .awake);
    }
    const ns: u64 = @intCast(start.untilNow(io).raw.toNanoseconds());
    sh.stop.store(true, .release);
    th.join();
    printLat("vacuum", sh, ns);
    std.debug.print("step={d} busy={d}% steps={d} step_p50_us<{d} step_max_ms={d} pages={d}->{d} moved={d} time_ms={d}\n", .{
        step, busy_pct, steps.n, steps.quantile(0.5), steps.max_ns / std.time.ns_per_ms, before, t.npages, moved, ns / std.time.ns_per_ms,
    });
    try t.check(gpa);
}

/// Scans `scan_len` keys in `scan_pct` percent of the operations, and updates any key (a get and then a put)
/// in `update_pct` percent. The other operations are gets, 9 of 10 to a hot key.
/// It runs in one thread, so the pool counters show which operation read which pages.
fn scanmix(t: *bpt.BPTree, io: Io, scan_pct: usize, update_pct: usize, ops: usize) !void {
    var prng: std.Random.DefaultPrng = .init(7);
    const rand = prng.random();
    var kbuf: [16]u8 = undefined;
    var hbuf: [16]u8 = undefined;
    var out: [max_test_val]u8 = undefined;
    const Count = struct {
        fn visit(_: void, _: []const u8, _: []const u8) !void {}
    };
    const pool = &t.pool;

    var get_lookups: u64 = 0;
    var get_reads: u64 = 0;
    var scan_reads: u64 = 0;
    const writes = pool.writes.raw;
    const syncs = pool.wal.syncs.raw;
    const moves = pool.hand.raw;
    const start = Io.Clock.Timestamp.now(io, .awake);
    for (0..ops) |_| {
        const lookups = pool.lookups.raw;
        const reads = pool.reads.raw;
        const roll = rand.uintLessThan(usize, 100);
        if (roll < scan_pct) {
            const lo = rand.uintLessThan(usize, bench_keys - scan_len);
            _ = try t.scan(keyOf(&kbuf, lo), keyOf(&hbuf, lo + scan_len), {}, Count.visit);
            scan_reads += pool.reads.raw - reads;
            continue;
        }
        if (roll < scan_pct + update_pct) {
            const key = keyOf(&kbuf, rand.uintLessThan(usize, bench_keys));
            const v = (try t.get(key, &out)).?;
            try t.put(key, v);
            continue;
        }
        // 9 of 10 gets go to a hot key, and the rest to any key.
        const k = if (rand.uintLessThan(usize, 10) < 9)
            rand.uintLessThan(usize, hot_runs) * (bench_keys / hot_runs) + rand.uintLessThan(usize, hot_len)
        else
            rand.uintLessThan(usize, bench_keys);
        _ = try t.get(keyOf(&kbuf, k), &out);
        get_lookups += pool.lookups.raw - lookups;
        get_reads += pool.reads.raw - reads;
    }
    const ns: u64 = @intCast(start.untilNow(io).raw.toNanoseconds());
    const hit = 100 * @as(f64, @floatFromInt(get_lookups - get_reads)) / @as(f64, @floatFromInt(get_lookups));
    std.debug.print("scans={d}% updates={d}% ops={d} time_ms={d} get_reads={d} get_hit_rate={d:.2}% scan_reads={d} writes={d} log_syncs={d} hand_moves={d}\n", .{
        scan_pct, update_pct, ops, ns / std.time.ns_per_ms, get_reads, hit, scan_reads, pool.writes.raw - writes, pool.wal.syncs.raw - syncs, pool.hand.raw - moves,
    });
}

/// Vacuums in steps of 16 pages, busy at most a quarter of the time, until `stop` is true.
const VacuumLoop = struct {
    t: *bpt.BPTree,
    stop: std.atomic.Value(bool) = .init(false),
    steps: u64 = 0,
    moved: u64 = 0,

    fn go(v: *VacuumLoop) void {
        while (!v.stop.load(.acquire)) {
            const s = v.t.vacuumOnline(.{ .incremental = 16 }, 16, 25) catch |err| {
                if (err != error.PoolExhausted) std.debug.panic("stress: vacuum: {t}", .{err});
                std.Thread.yield() catch {};
                continue;
            };
            v.steps += 1;
            v.moved += s.moved;
        }
    }
};

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
    var vbuf: [max_test_val]u8 = undefined;
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
    var vbuf: [max_test_val]u8 = undefined;
    t.durable = false;
    for (0..test_keys) |k| try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, 1));
    try t.sync();
    t.durable = true;
    for (0..crash_threads) |id| _ = try std.Thread.spawn(.{}, crashWorker, .{ &t, id, seed + id });
    try io.sleep(.fromMilliseconds(@intCast(ms)), .awake);
    // Like a crash of the process: no sync, no deinit, and the threads stop wherever they are.
    std.process.exit(0);
}

/// Loads `bench_keys` keys, one value in four with a chain, and deletes all but `keep_pct` percent of them.
/// Then it runs one vacuum with `mode`. It prints the size of the file after each step.
fn shrink(t: *bpt.BPTree, io: Io, file: Io.File, keep_pct: usize, mode: bpt.BPTree.VacuumMode) !void {
    var kbuf: [16]u8 = undefined;
    var vbuf: [max_test_val]u8 = undefined;
    t.durable = false;
    for (0..bench_keys) |k| try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, 1));
    try t.sync();
    const loaded = try file.length(io);
    var prng: std.Random.DefaultPrng = .init(11);
    const rand = prng.random();
    for (0..bench_keys) |k| {
        if (rand.uintLessThan(usize, 100) >= keep_pct) _ = try t.delete(keyOf(&kbuf, k));
    }
    try t.sync();
    const deleted = try file.length(io);
    const writes = t.pool.writes.raw;
    const start = Io.Clock.Timestamp.now(io, .awake);
    const s = try t.vacuum(mode);
    const ns: u64 = @intCast(start.untilNow(io).raw.toNanoseconds());
    std.debug.print("keep={d}% mode={t} loaded_kb={d} deleted_kb={d} vacuum_kb={d} pages={d}->{d} moved={d} page_writes={d} time_ms={d}\n", .{
        keep_pct, mode, loaded / 1024, deleted / 1024, try file.length(io) / 1024, s.before, s.after, s.moved, t.pool.writes.raw - writes, ns / std.time.ns_per_ms,
    });
}

/// Ends the process after `ms` milliseconds, like a crash.
fn exitAfter(io: Io, ms: u64) void {
    io.sleep(.fromMilliseconds(@intCast(ms)), .awake) catch {};
    std.process.exit(0);
}

/// Fills a new tree in `path` and syncs it. Then it changes keys and vacuums the tree in a loop,
/// until the process ends after `ms` milliseconds, often in the middle of a vacuum.
fn vacuumCrash(io: Io, gpa: std.mem.Allocator, path: []const u8, seed: u64, ms: u64) !void {
    const f: Files = try .open(io, path, true);
    var t: bpt.BPTree = try .init(gpa, io, f.file, f.log);
    var kbuf: [16]u8 = undefined;
    var vbuf: [max_test_val]u8 = undefined;
    t.durable = false;
    for (0..test_keys) |k| try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, 1));
    try t.sync();
    _ = try std.Thread.spawn(.{}, exitAfter, .{ io, ms });
    var prng: std.Random.DefaultPrng = .init(seed);
    const rand = prng.random();
    while (true) {
        // Deletes free pages all over the file, and puts take some of them again.
        for (0..500) |_| {
            const k = rand.uintLessThan(usize, test_keys);
            if (rand.uintLessThan(usize, 10) < 6) {
                _ = try t.delete(keyOf(&kbuf, k));
            } else try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, rand.int(u32) | 1));
        }
        _ = try t.vacuum(switch (rand.uintLessThan(usize, 3)) {
            0 => .truncate,
            1 => .full,
            else => .{ .incremental = rand.uintLessThan(u32, 200) },
        });
    }
}

/// Like `crash`, but the main thread also vacuums the tree in steps while the writers run, as a service would.
/// The process ends after `ms` milliseconds, in the middle of the operations and of a step.
fn onlineCrash(io: Io, gpa: std.mem.Allocator, path: []const u8, seed: u64, ms: u64) !void {
    const f: Files = try .open(io, path, true);
    var t: bpt.BPTree = try .init(gpa, io, f.file, f.log);
    var kbuf: [16]u8 = undefined;
    var vbuf: [max_test_val]u8 = undefined;
    t.durable = false;
    for (0..test_keys) |k| try t.put(keyOf(&kbuf, k), makeVal(&vbuf, k, 1));
    try t.sync();
    t.durable = true;
    for (0..crash_threads) |id| _ = try std.Thread.spawn(.{}, crashWorker, .{ &t, id, seed + id });
    _ = try std.Thread.spawn(.{}, exitAfter, .{ io, ms });
    while (true) _ = t.vacuumOnline(.full, 32, 50) catch |err| if (err != error.PoolExhausted) return err;
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
    if (std.mem.eql(u8, mode, "vaccrash") and args.len > 4)
        return vacuumCrash(io, gpa, args[2], try arg(args, 3, 1), try arg(args, 4, 100));
    if (std.mem.eql(u8, mode, "onlinecrash") and args.len > 4)
        return onlineCrash(io, gpa, args[2], try arg(args, 3, 1), try arg(args, 4, 100));

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
        var vbuf: [max_test_val]u8 = undefined;
        var out: [max_test_val]u8 = undefined;
        for (0..rounds) |round| {
            // A thread vacuums in steps while the workers run.
            var vac: VacuumLoop = .{ .t = &t };
            const vt = try std.Thread.spawn(.{}, VacuumLoop.go, .{&vac});
            try run(testWorker, &sh, 1 + round * 1000);
            vac.stop.store(true, .release);
            vt.join();
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
            // Vacuum, and check the tree again. The next round runs on the shorter file.
            const vs = try t.vacuum(.full);
            try t.check(gpa);
            c = .{ .sh = &sh, .id = null, .lo = 0, .hi = test_keys - 1, .next = 0 };
            if (try t.scan(null, null, &c, ScanCheck.visit) != present) fail("scan after vacuum: wrong key count", .{});
            c.missing(test_keys);
            try t.sync();
            std.debug.print("round {d}: ok, {d} keys, {d} vacuum steps moved {d} pages, vacuum {d} -> {d} pages, {d} moved\n", .{ round, present, vac.steps, vac.moved, vs.before, vs.after, vs.moved });
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
        const locks = t.pool.locks.raw;
        const start = Io.Clock.Timestamp.now(io, .awake);
        try run(benchWorker, &sh, 7);
        const ns: u64 = @intCast(start.untilNow(io).raw.toNanoseconds());
        const total = sh.threads * sh.ops;
        std.debug.print("threads={d} reads={d}% ops={d} time_ms={d} ops_per_s={d} retries={d} log_syncs={d} pool_locks_per_op={d:.2}\n", .{
            sh.threads,                     sh.read_pct,    total,                        ns / std.time.ns_per_ms,
            total * std.time.ns_per_s / ns, sh.retries.raw, t.pool.wal.syncs.raw - syncs, @as(f64, @floatFromInt(t.pool.locks.raw - locks)) / @as(f64, @floatFromInt(total)),
        });
    } else if (std.mem.eql(u8, mode, "shrink")) {
        const vmode: bpt.BPTree.VacuumMode = if (args.len > 3 and std.mem.eql(u8, args[3], "truncate"))
            .truncate
        else if (args.len > 3 and !std.mem.eql(u8, args[3], "full"))
            .{ .incremental = try std.fmt.parseInt(u32, args[3], 10) }
        else
            .full;
        try shrink(&t, io, f.file, try arg(args, 2, 25), vmode);
    } else if (std.mem.eql(u8, mode, "online")) {
        var sh: Shared = .{ .t = &t, .threads = try arg(args, 2, 4), .read_pct = try arg(args, 5, 90), .ops = 0 };
        try online(&t, io, gpa, &sh, @intCast(try arg(args, 3, 256)), @intCast(try arg(args, 4, 25)));
    } else if (std.mem.eql(u8, mode, "scanmix")) {
        var kbuf: [16]u8 = undefined;
        const val: [50]u8 = @splat('v');
        t.durable = false;
        for (0..bench_keys) |k| try t.put(keyOf(&kbuf, k), &val);
        try t.sync();
        t.durable = args.len <= 5 or !std.mem.eql(u8, args[5], "nosync");
        try scanmix(&t, io, try arg(args, 2, 5), try arg(args, 3, 0), try arg(args, 4, 50000));
    } else {
        std.debug.print("usage: stress test [threads] [ops] [rounds] | stress bench [threads] [read%] [ops]" ++
            " | stress scanmix [scan%] [update%] [ops] [nosync] | stress crash <file> <seed> <ms> | stress verify <file>" ++
            " | stress shrink [keep%] [truncate|full|pages] | stress vaccrash <file> <seed> <ms>" ++
            " | stress online [threads] [step] [busy%] [read%] | stress onlinecrash <file> <seed> <ms>\n", .{});
        return error.BadArgs;
    }
}
