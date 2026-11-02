#!/bin/sh
# Usage: Fuzz/build.sh <build-dir> [jobs]
# Builds <build-dir>/fuzz, <build-dir>/lines and <build-dir>/port_test, runs port_test, replays an assertion input,
# and runs lines on all small "pop"
# cases (pop_cases.sh), "spill" cases (spill_cases.sh), "surplus" cases (surplus_cases.sh), "permute" cases
# (permute_cases.sh), "lowest" cases (lowest_cases.sh), "map" cases (map_cases.sh), "resolve" cases
# (resolve_cases.sh) and "plan" cases (plan_cases.sh), and ci_test.sh. Run it from the repository root inside
# `nix develop`, and again after a change to the Lean model, to solidity or to the kraken/c asm.
# [jobs] is the number of parallel ninja jobs (default: the ninja default).
set -eu
build=$1
jobs=${2:-}
mkdir -p "$build"
lake build ShufflerKraken/bbuAssembly Fuzz
cmake -S . -B build -G Ninja -DBUILD_TESTING=ON
cmake --build build --target shuffler_test_assembly
# Init, Std and Lean are in libleanshared and Lake is in libLake_shared. The Lean model is compiled
# from C with coverage instrumentation, every other imported module is linked as an object.
lake env lean --run Fuzz/closure.lean Fuzz.Oracle | grep -vE '^(Init|Std|Lean|Lake)(\.|$)' > "$build/modules.txt"
grep -E '^(Shuffler|Fuzz)(\.|$)' "$build/modules.txt" | sed 's/.*/+&:c/' | xargs lake query > "$build/lean-sources.txt"
grep -vE '^(Shuffler|Fuzz)(\.|$)' "$build/modules.txt" | sed 's/.*/+&:o/' | xargs lake query > "$build/lean-objects.txt"
cmake -S Fuzz -B "$build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DLEAN_PREFIX="$(lean --print-prefix)" \
  -DLEAN_SOURCES="$build/lean-sources.txt" -DLEAN_OBJECTS="$build/lean-objects.txt" \
  -DIGNORE_VENDORED_DEPENDENCIES=ON -DBoost_USE_STATIC_LIBS=OFF -DTESTS=OFF -DTOOLS=OFF -DPEDANTIC=OFF
ninja -C "$build" ${jobs:+-j "$jobs"} fuzz lines port_test
"$build/port_test"
# This input decodes to a pop of an empty stack. Its assembly assertion must
# return err to the parent without triggering libFuzzer's exit handler.
printf '\006\000\000\000\000\000\000\000\000\001' > "$build/assertion-pop.input"
"$build/fuzz" -runs=1 "$build/assertion-pop.input"
sh "$(dirname "$0")/pop_cases.sh" 5 | "$build/lines"
sh "$(dirname "$0")/spill_cases.sh" 4 | "$build/lines"
sh "$(dirname "$0")/surplus_cases.sh" 4 2 | "$build/lines"
sh "$(dirname "$0")/permute_cases.sh" 4 | "$build/lines"
sh "$(dirname "$0")/lowest_cases.sh" 4 | "$build/lines"
sh "$(dirname "$0")/map_cases.sh" 3 | "$build/lines"
sh "$(dirname "$0")/resolve_cases.sh" | "$build/lines"
sh "$(dirname "$0")/plan_cases.sh" 2 | "$build/lines"
sh "$(dirname "$0")/ci_test.sh"
