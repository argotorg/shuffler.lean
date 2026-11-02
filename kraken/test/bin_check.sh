#!/usr/bin/env bash
# Compare the program of `FlatShuffler.binHost` (FlatShuffler/Bin.lean) with the code in the
# binary build/kraken/c/bbu_harness: each instruction must have the same address, size and text.
# Kraken's AT&T printer prints the program, objdump disassembles the binary, and
# test/bin_check.awk compares the two (its header lists the normal form rules).
#
# With a directory argument, also keep the two listings there.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$dir/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cmake -S "$root" -B "$root/build" -G Ninja -DBUILD_TESTING=ON >/dev/null
cmake --build "$root/build" --target shuffler_bbu_harness >/dev/null
(cd "$root" && lake build -q FlatShuffler.Bin Kraken.X64.PrintATT >/dev/null)
(cd "$root" && lake env lean -DElab.async=false --run kraken/test/BinHostMain.lean) > "$tmp/host"
"$dir/test/bin_objdump.sh" "$root/build/kraken/c/bbu_harness" > "$tmp/dis"
if [ $# -gt 0 ]; then cp "$tmp/host" "$tmp/dis" "$1"; fi
awk -f "$dir/test/bin_check.awk" "$tmp/host" "$tmp/dis"
