#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${PERMUTE_AFL_BUILD:-"$test_dir/../build/afl"}
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
exec afl-fuzz -i "$build_dir/seeds" -o "$build_dir/findings" \
    -m none -t 10000 -G 8195 -s 2654435769 "$@" -- "$build_dir/permute-afl"
