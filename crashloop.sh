#!/bin/sh
# Crashes the tree N times at random moments and checks it after each crash.
N=${1:-20}
zig build -Doptimize=ReleaseSafe || exit 1
bad=0
for i in $(seq 1 $N); do
    ./zig-out/bin/stress crash crash.bin $i $((20 + i * 37 % 300)) || exit 1
    if ! ./zig-out/bin/stress verify crash.bin; then bad=$((bad + 1)); fi
done
rm -f crash.bin crash.bin.wal
echo "$bad of $N crashes left a broken tree"
