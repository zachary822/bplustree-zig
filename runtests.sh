#!/bin/sh
# Runs the unit tests with several settings, then the stress test in five builds.
# Stops at the first failure.
set -e
THREADS=${THREADS:-8}
OPS=${OPS:-20000}
zig build test --summary all
zig build test --summary all -Dpool_frames=4
zig build test --summary all -Dpool_frames=64
zig build test --summary all -Dpage_size=8192 -Dpool_frames=64
zig build test --summary all -Dparanoid=true
zig build stress -Dtsan=true -- test $THREADS $OPS
zig build stress -Doptimize=ReleaseSafe -Dpool_frames=8 -- test $THREADS $OPS
zig build stress -Dtsan=true -Dpage_size=512 -- test $THREADS $OPS
zig build stress -Doptimize=ReleaseSafe -Dpage_size=512 -- test $THREADS $OPS
zig build stress -Dparanoid=true -Dpage_size=512 -- test $THREADS $OPS
echo "all builds passed"
