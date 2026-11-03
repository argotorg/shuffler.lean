#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
core=${1:-"$test_dir/../permute.c"}
build_dir=${2:-"$test_dir/../build/tests"}
test_flags=${PERMUTE_TEST_FLAGS:--O2}
oracle_dir=${PERMUTE_ORACLE_DIR:-"$build_dir/oracle"}
cc=${CC:-cc}
cxx=${CXX:-c++}
if [ ! -f "$core" ]; then
    printf 'generated C file is missing: %s\n' "$core" >&2
    exit 1
fi
mkdir -p "$build_dir"
python3 "$test_dir/prepare_oracle.py" "$oracle_dir"
python3 "$test_dir/test_prepare_oracle.py" "$oracle_dir"
"$cc" --version | head -n 1
"$cc" -dumpmachine
printf 'test flags: %s\n' "$test_flags"
# Word splitting in test_flags is intentional. It is a list of compiler flags.
# Compile the generated core as C, even though the oracle needs a C++ linker.
"$cc" -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
    $test_flags -I "$test_dir/.." -c "$core" -o "$build_dir/permute.o"
"$cxx" -std=c++20 -pedantic-errors -Wall -Wextra $test_flags \
    -I "$oracle_dir" -c "$test_dir/oracle.cpp" -o "$build_dir/oracle.o"
"$cc" -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
    $test_flags -c "$test_dir/check_case.c" -o "$build_dir/check_case.o"
for driver in tests fuzz; do
    "$cc" -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
        $test_flags -c "$test_dir/$driver.c" -o "$build_dir/$driver.o"
    "$cxx" $test_flags "$build_dir/permute.o" "$build_dir/oracle.o" \
        "$build_dir/check_case.o" "$build_dir/$driver.o" -o "$build_dir/$driver"
done
"$build_dir/tests"
"$build_dir/fuzz" "${PERMUTE_FUZZ_CASES:-20000}" "${PERMUTE_FUZZ_SEED:-2654435769}"
