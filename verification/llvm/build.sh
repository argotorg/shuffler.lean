#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
base=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
clight_source=${clightSource:-"$base/../../spikes/clight-permute"}
mkdir -p "$base/build/clight" "$base/build/project" "$base/artifacts"
cp "$clight_source/Permute.v" "$clight_source/build-deps.sh" \
  "$clight_source/audit-deps.py" "$clight_source/check-assumptions.py" \
  "$base/build/clight/"
cp -R "$clight_source/vendor" "$base/build/clight/"
sh "$base/build/clight/build-deps.sh"
cp "$base"/*.v "$base/build/project/"
cp "$clight_source/Permute.v" "$clight_source/printer.ml" \
  "$base/print_source.ml" "$base/print_llvm.ml" "$base/build/project/"
cd "$base/build/project"

check() { coqc -R ../clight/build/compcert compcert "$@"; }
check Permute.v
check ClightDepth.v
check ExtractSource.v
ocamlc -c extracted.mli
ocamlc -w -a -c extracted.ml
ocamlc -o print-source extracted.cmo printer.ml print_source.ml
./print-source > depth.c
clang -std=c11 -O2 -fno-discard-value-names -emit-llvm -S depth.c -o depth.ll
opt -passes=verify -disable-output depth.ll
frontend -op . depth.ll > frontend.log
python3 "$base/import_ast.py" depth.v.ast Candidate.v
check Normalize.v
check Candidate.v
check Program.v
check PureResult.v
check Equivalence.v
check Assumptions.v > assumptions.txt
check Export.v
ocamlc -c exported.mli
ocamlc -w -a -c exported.ml
ocamlc -o print-llvm exported.cmo print_llvm.ml
./print-llvm > depth.proved.ll
llvm-as depth.proved.ll -o depth.proved.bc
opt -passes=verify -disable-output depth.proved.bc
clang -Wno-unused-command-line-argument -O2 -c depth.proved.ll -o depth.proved.o

python3 "$base/test_import.py"
python3 "$base/test_pipeline.py" "$PWD"
cp depth.c depth.ll Candidate.v assumptions.txt \
  depth.proved.ll depth.proved.bc depth.proved.o "$base/artifacts/"
mkdir -p "$base/artifacts/proof"
cp ./*.v ./*.vo "$base/artifacts/proof/"
cp -R ../clight/build/compcert "$base/artifacts/proof/"
clang --version > "$base/artifacts/clang-version.txt"
coqc --version > "$base/artifacts/rocq-version.txt"
