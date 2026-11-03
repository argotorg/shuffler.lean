#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${1:-"$test_dir/../build/afl"}
mkdir -p "$build_dir"
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
python3 "$test_dir/prepare_oracle.py" "$build_dir/oracle"
python3 "$test_dir/test_prepare_oracle.py" "$build_dir/oracle"
afl_root=$(dirname -- "$(dirname -- "$(command -v afl-fuzz)")")
driver=${AFL_DRIVER:-"$afl_root/lib/afl/libAFLDriver.a"}
test -f "$driver"
afl-clang-fast --version | head -n 1
afl-clang-fast -dumpmachine
flags='-O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fno-sanitize-recover=all'
for unit in permute check_case guided; do
    case "$unit" in
        permute) source="$test_dir/../permute.c" ;;
        *) source="$test_dir/$unit.c" ;;
    esac
    afl-clang-fast -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
        $flags -c "$source" -o "$build_dir/$unit.o"
done
afl-clang-fast++ -std=c++20 -pedantic-errors -Wall -Wextra $flags \
    -I "$build_dir/oracle" -c "$test_dir/oracle.cpp" -o "$build_dir/oracle.o"
afl-clang-fast++ $flags "$build_dir/permute.o" "$build_dir/check_case.o" \
    "$build_dir/guided.o" "$build_dir/oracle.o" "$driver" -o "$build_dir/permute-afl"
python3 "$test_dir/seed_corpus.py" "$build_dir/seeds"
printf 'AFL++ target: %s/permute-afl\n' "$build_dir"
