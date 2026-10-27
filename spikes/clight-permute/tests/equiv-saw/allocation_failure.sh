#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$test_dir/../.." && pwd)
build="$root/build/equiv-saw/allocation-failure"
mkdir -p "$build"
python3 "$root/tests/prepare_oracle.py" "$build/oracle"
clang -std=c11 -O1 -c "$root/permute.c" -o "$build/core.o"
clang++ -std=c++20 -O0 -I "$build/oracle" -c "$root/tests/oracle.cpp" -o "$build/oracle.o"
clang++ -std=c++20 -O0 "$test_dir/allocation_failure.cpp" "$build/core.o" \
    "$build/oracle.o" -Wl,--wrap=_Znwm -o "$build/check"
"$build/check"
