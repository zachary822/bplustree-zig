const std = @import("std");
const Io = std.Io;

const bplustree_zig = @import("bplustree_zig");

pub fn main(init: std.process.Init) !u8 {
    const gpa = init.gpa;
    const arena = init.arena;
    const args = try init.minimal.args.toSlice(arena.allocator());

    if (args.len < 2) {
        std.log.err("pass in tree file", .{});
        return 1;
    }

    var t: bplustree_zig.BPTree = try .init(gpa, init.io, Io.Dir.cwd(), args[1]);
    defer t.deinit(gpa);

    try t.sync();
    return 0;
}
