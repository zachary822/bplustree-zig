const std = @import("std");
const Io = std.Io;

const bplustree_zig = @import("bplustree_zig");

pub fn main(init: std.process.Init) !u8 {
    const gpa = init.gpa;
    const io = init.io;
    const arena = init.arena;
    const args = try init.minimal.args.toSlice(arena.allocator());

    if (args.len < 2) {
        std.log.err("pass in tree file", .{});
        return 1;
    }

    const file = try Io.Dir.cwd().createFile(init.io, args[1], .{ .read = true, .truncate = false });
    defer file.close(io);
    var logs: [2]Io.File = undefined;
    for (&logs, 0..) |*log, i| {
        const log_name = try std.fmt.allocPrint(arena.allocator(), "{s}.wal{d}", .{ args[1], i });
        log.* = try Io.Dir.cwd().createFile(init.io, log_name, .{ .read = true, .truncate = false });
    }
    defer for (logs) |log| log.close(io);

    var t: bplustree_zig.BPTree = try .init(gpa, io, file, logs);
    defer t.deinit();

    try t.sync();
    return 0;
}
