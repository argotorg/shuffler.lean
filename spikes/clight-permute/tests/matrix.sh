#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
core=${1:-"$test_dir/../permute.c"}
build_dir=${2:-"$test_dir/../build/tests"}
for compiler in gcc clang; do
    case "$compiler" in
        gcc) cxx=g++ ;;
        clang) cxx=clang++ ;;
    esac
    for mode in O2 O3 sanitize; do
        case "$mode" in
            O2) flags='-O2 -fstrict-aliasing' ;;
            O3) flags='-O3 -fstrict-aliasing' ;;
            sanitize) flags='-O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fno-sanitize-recover=all' ;;
        esac
        CC=$compiler CXX=$cxx PERMUTE_TEST_FLAGS=$flags \
            PERMUTE_ORACLE_DIR="$build_dir/oracle" \
            sh "$test_dir/run.sh" "$core" "$build_dir/$compiler-$mode"
    done
done
