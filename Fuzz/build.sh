#!/bin/sh
# Usage: Fuzz/build.sh <build-dir>
# Builds <build-dir>/fuzz. Run it from the repository root inside `nix develop`, and again after a
# change to the Lean model or to solidity.
set -eu
build=$1
mkdir -p "$build"
lake build Fuzz
# Init, Std and Lean are in libleanshared and Lake is in libLake_shared. The Lean model is compiled
# from C with coverage instrumentation, every other imported module is linked as an object.
lake env lean --run Fuzz/closure.lean Fuzz.Oracle | grep -vE '^(Init|Std|Lean|Lake)(\.|$)' > "$build/modules.txt"
grep -E '^(Shuffler|Fuzz)(\.|$)' "$build/modules.txt" | sed 's/.*/+&:c/' | xargs lake query > "$build/lean-sources.txt"
grep -vE '^(Shuffler|Fuzz)(\.|$)' "$build/modules.txt" | sed 's/.*/+&:o/' | xargs lake query > "$build/lean-objects.txt"
cmake -S Fuzz -B "$build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DLEAN_PREFIX="$(lean --print-prefix)" \
  -DLEAN_SOURCES="$build/lean-sources.txt" -DLEAN_OBJECTS="$build/lean-objects.txt" \
  -DIGNORE_VENDORED_DEPENDENCIES=ON -DBoost_USE_STATIC_LIBS=OFF -DTESTS=OFF -DTOOLS=OFF -DPEDANTIC=OFF
ninja -C "$build" fuzz
