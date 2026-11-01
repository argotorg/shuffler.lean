#!/usr/bin/env bash
# Compare the program of `Bbu.binHost` (BbuKraken/Bin.lean) with the code in the
# binary c/bbu_harness: each instruction must have the same address, size and text.
# Kraken's AT&T printer prints the program, objdump disassembles the binary, and
# test/bin_check.awk compares the two (its header lists the normal form rules).
#
# With a directory argument, also keep the two listings there.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$dir/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

make -C "$dir/c" -s bbu_harness
(cd "$root" && lake build -q BbuKraken.Bin Kraken.X64.PrintATT >/dev/null)
(cd "$root" && lake env lean --run kraken/test/BinHostMain.lean) > "$tmp/host"
"$dir/test/bin_objdump.sh" "$dir/c/bbu_harness" > "$tmp/dis"
if [ $# -gt 0 ]; then cp "$tmp/host" "$tmp/dis" "$1"; fi
awk -f "$dir/test/bin_check.awk" "$tmp/host" "$tmp/dis"
