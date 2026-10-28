#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
if [ "$#" -lt 1 ]; then
  printf 'usage: export.sh COMPCERT [COQC_LOAD_PATH_ARGUMENTS...]\n' >&2
  exit 2
fi
compcert=$1
shift
# Run from the checked proof directory. FullContract.vo must already exist.
coqc -R "$compcert" compcert "$@" FullExport.v
ocamlc -c full_exported.mli
ocamlc -w -a -c full_exported.ml
ocamlc -o print-full full_exported.cmo print_full.ml
./print-full > permute.proved.ll
llvm-as permute.proved.ll -o permute.proved.bc
opt -passes=verify -disable-output permute.proved.bc
clang -Wno-unused-command-line-argument -O2 -fPIC -c permute.proved.ll -o permute.proved.o
