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
    const log_name = try std.fmt.allocPrint(arena.allocator(), "{s}.wal", .{args[1]});
    const log = try Io.Dir.cwd().createFile(init.io, log_name, .{ .read = true, .truncate = false });
    defer log.close(io);

    var t: bplustree_zig.BPTree = try .init(gpa, io, file, log);
    defer t.deinit(gpa);

    try t.sync();
    return 0;
}
