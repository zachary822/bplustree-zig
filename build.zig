const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const page_size = b.option(usize, "page_size", "Size of b+ tree page.") orelse 4096;
    const pool_frames = b.option(usize, "pool_frames", "Size of b+ tree pool") orelse 16;
    const max_usage = b.option(u8, "max_usage", "Highest usage count of a frame") orelse 5;
    const pool_paranoid = b.option(bool, "paranoid", "Paranoid mode") orelse false;
    const disk_delay_us = b.option(u32, "disk_delay_us", "Sleep this long in every page read and write") orelse 0;
    const tsan = b.option(bool, "tsan", "Build with ThreadSanitizer") orelse false;

    const options = b.addOptions();
    options.addOption(usize, "page_size", page_size);
    options.addOption(usize, "pool_frames", pool_frames);
    options.addOption(u8, "max_usage", max_usage);
    options.addOption(bool, "pool_paranoid", pool_paranoid);
    options.addOption(u32, "disk_delay_us", disk_delay_us);

    const mod = b.addModule("bplustree_zig", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .sanitize_thread = tsan,
    });
    mod.addOptions("build_options", options);

    const exe = b.addExecutable(.{
        .name = "bplustree_zig",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .sanitize_thread = tsan,
            .imports = &.{
                .{ .name = "bplustree_zig", .module = mod },
            },
        }),
    });

    b.installArtifact(exe);

    const run_step = b.step("run", "Run the app");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());
    run_cmd.addPassthruArgs();

    // The stress test and benchmark. Pass the mode and its arguments after `--`,
    // like this: `zig build stress -- bench 4 90 50000`
    const stress_exe = b.addExecutable(.{
        .name = "stress",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/stress.zig"),
            .target = target,
            .optimize = optimize,
            .sanitize_thread = tsan,
            .imports = &.{
                .{ .name = "bplustree_zig", .module = mod },
            },
        }),
    });
    b.installArtifact(stress_exe);

    const stress_step = b.step("stress", "Run the stress test or the benchmark");
    const stress_cmd = b.addRunArtifact(stress_exe);
    stress_step.dependOn(&stress_cmd.step);
    stress_cmd.step.dependOn(b.getInstallStep());
    stress_cmd.addPassthruArgs();

    const mod_tests = b.addTest(.{ .root_module = mod });
    const run_mod_tests = b.addRunArtifact(mod_tests);
    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_mod_tests.step);
}
