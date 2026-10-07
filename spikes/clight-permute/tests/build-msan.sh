#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${1:-"$test_dir/../build/msan"}
: "${MSAN_LLVM_SOURCE:?use tests/msan-shell.nix}"
mkdir -p "$build_dir"
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
clang --version
cmake --version | head -n 1
ninja --version
cmake -G Ninja -S "$MSAN_LLVM_SOURCE/runtimes" -B "$build_dir/runtime" \
    -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
    -DCMAKE_INSTALL_PREFIX="$build_dir/runtime-install" \
    '-DLLVM_ENABLE_RUNTIMES=libunwind;libcxxabi;libcxx' \
    -DLLVM_USE_SANITIZER=MemoryWithOrigins \
    -DLIBCXX_ENABLE_SHARED=OFF -DLIBCXX_ENABLE_STATIC=ON \
    -DLIBCXXABI_ENABLE_SHARED=OFF -DLIBCXXABI_ENABLE_STATIC=ON \
    -DLIBUNWIND_ENABLE_SHARED=OFF -DLIBUNWIND_ENABLE_STATIC=ON \
    -DLIBCXXABI_USE_LLVM_UNWINDER=ON -DLIBCXXABI_USE_COMPILER_RT=ON \
    -DLIBUNWIND_USE_COMPILER_RT=ON -DLIBCXX_USE_COMPILER_RT=ON \
    -DLIBCXX_INCLUDE_TESTS=OFF -DLIBCXXABI_INCLUDE_TESTS=OFF \
    -DLIBUNWIND_INCLUDE_TESTS=OFF -DLLVM_INCLUDE_TESTS=OFF
cmake --build "$build_dir/runtime" --parallel "${MSAN_BUILD_JOBS:-4}"
cmake --install "$build_dir/runtime"
python3 "$test_dir/prepare_oracle.py" "$build_dir/oracle"
python3 "$test_dir/test_prepare_oracle.py" "$build_dir/oracle"
flags='-O1 -g -fno-omit-frame-pointer -fPIE -fsanitize=memory -fsanitize-memory-track-origins=2 -fno-sanitize-recover=all'
include="$build_dir/runtime-install/include/c++/v1"
library="$build_dir/runtime-install/lib"
# The packaged libFuzzer uses libstdc++. Build its unchanged sources against
# the instrumented libc++ as well. Do not instrument the driver for coverage.
mkdir -p "$build_dir/fuzzer"
for source in "$MSAN_LLVM_SOURCE"/compiler-rt/lib/fuzzer/*.cpp; do
    unit=$(basename -- "$source" .cpp)
    clang++ -std=c++17 $flags -nostdinc++ -isystem "$include" \
        -I "$MSAN_LLVM_SOURCE/compiler-rt/include" \
        -c "$source" -o "$build_dir/fuzzer/$unit.o"
done
llvm-ar rcs "$build_dir/libFuzzer.a" "$build_dir"/fuzzer/*.o
for unit in permute check_case guided; do
    case "$unit" in
        permute) source="$test_dir/../permute.c" ;;
        *) source="$test_dir/$unit.c" ;;
    esac
    clang -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
        $flags -fsanitize=fuzzer-no-link -c "$source" -o "$build_dir/$unit.o"
done
clang++ -std=c++20 -pedantic-errors -Wall -Wextra $flags -fsanitize=fuzzer-no-link \
    -nostdinc++ -isystem "$include" -I "$build_dir/oracle" \
    -c "$test_dir/oracle.cpp" -o "$build_dir/oracle.o"
# A fixed low code address avoids high-entropy PIE placement in MSan shadow
# space on this host. Shared libraries remain dynamic; ASLR stays enabled.
clang++ $flags -no-pie -nostdlib++ \
    "$build_dir/permute.o" "$build_dir/check_case.o" "$build_dir/guided.o" \
    "$build_dir/oracle.o" "$build_dir/libFuzzer.a" "$library/libc++.a" "$library/libc++abi.a" \
    "$library/libunwind.a" -pthread -ldl -lm -o "$build_dir/permute-msan"
clang++ -std=c++20 $flags -no-pie -nostdinc++ -isystem "$include" -nostdlib++ \
    "$test_dir/msan-probe.cpp" "$library/libc++.a" "$library/libc++abi.a" \
    "$library/libunwind.a" -pthread -ldl -lm -o "$build_dir/msan-probe"
printf 'MSan target: %s/permute-msan\n' "$build_dir"
