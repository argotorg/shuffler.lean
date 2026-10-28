#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
base=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
llvm_source=$(CDPATH= cd -- "$base/.." && pwd)
repository=$(CDPATH= cd -- "$base/../../.." && pwd)
build=${1:-"$llvm_source/build/full/candidate"}
c_source=${2:-"$repository/spikes/clight-permute/permute.c"}
mkdir -p "$build"
build=$(CDPATH= cd -- "$build" && pwd)
cp "$llvm_source/Normalize.v" "$base/candidate/"*.v "$build/"
cd "$build"
clang --target=x86_64-unknown-linux-gnu -std=c11 -O1 \
  -fno-builtin -fno-vectorize -fno-slp-vectorize \
  -fno-discard-value-names -emit-llvm -S \
  "$c_source" -o permute.ll
opt -passes=verify -disable-output permute.ll
frontend -op . permute.ll > frontend.log
python3 "$llvm_source/import_ast.py" permute.v.ast FullCandidate.v
for module in Normalize FullNormalize NormalizeTests FullCandidate FullProgram FullCFG; do
  coqc "$module.v"
done
printf 'Full permute AST prepared and checked; semantic equivalence is not yet proved.\n'
