#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${1:-"$test_dir/../build/guided"}
mkdir -p "$build_dir"
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
python3 "$test_dir/coverage-manifest.py" clear "$build_dir"
python3 "$test_dir/prepare_oracle.py" "$build_dir/oracle"
python3 "$test_dir/test_prepare_oracle.py" "$build_dir/oracle"
clang --version | head -n 1
clang -dumpmachine
llvm-cov --version | head -n 2
python3 "$test_dir/coverage-manifest.py" begin "$build_dir"
for mode in fuzz coverage; do
    mkdir -p "$build_dir/$mode"
    case "$mode" in
        fuzz) flags='-O1 -g -fno-omit-frame-pointer -fsanitize=fuzzer-no-link,address,undefined -fno-sanitize-recover=all'
              link='-fsanitize=fuzzer,address,undefined -fno-sanitize-recover=all' ;;
        coverage) flags='-O0 -g -fprofile-instr-generate -fcoverage-mapping'
                  link='-fsanitize=fuzzer -fprofile-instr-generate' ;;
    esac
    # Compile the verified core as C. Only the solc adapter uses C++.
    for unit in permute check_case guided; do
        case "$unit" in
            permute) source="$test_dir/../permute.c" ;;
            *) source="$test_dir/$unit.c" ;;
        esac
        clang -std=c11 -pedantic-errors -Wall -Wextra -Wconversion -Wsign-conversion \
            $flags -c "$source" -o "$build_dir/$mode/$unit.o"
    done
    clang++ -std=c++20 -pedantic-errors -Wall -Wextra $flags \
        -I "$build_dir/oracle" -c "$test_dir/oracle.cpp" -o "$build_dir/$mode/oracle.o"
    clang++ $link "$build_dir/$mode/permute.o" "$build_dir/$mode/check_case.o" \
        "$build_dir/$mode/guided.o" "$build_dir/$mode/oracle.o" -o "$build_dir/$mode/permute-fuzz"
done
python3 "$test_dir/coverage-manifest.py" finish "$build_dir"
mkdir -p "$build_dir/corpus" "$build_dir/artifacts"
python3 "$test_dir/seed_corpus.py" "$build_dir/corpus"
printf 'Fuzzer: %s/fuzz/permute-fuzz\nCorpus: %s/corpus\n' "$build_dir" "$build_dir"
