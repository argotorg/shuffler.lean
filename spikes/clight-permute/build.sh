#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
spike_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$spike_dir"
sh build-deps.sh
python3 test-audit.py
mkdir -p build/project
cp Permute.v Extract.v printer.ml print_main.ml test_printer.ml permute.h build/project/
cd build/project
coqc -R ../compcert compcert Permute.v
coqc -R ../compcert compcert Extract.v
ocamlc -w +a-4-70 -c extracted.mli
ocamlc -w -a -c extracted.ml
ocamlc -w +a-4-70 -c printer.ml
ocamlc -w +a-4-70 -o test-printer extracted.cmo printer.cmo test_printer.ml
./test-printer
ocamlc -w +a-4-70 -o print-permute extracted.cmo printer.cmo print_main.ml
./print-permute > permute.c
cmp permute.c "$spike_dir/permute.c"
printf 'Generated C matches permute.c\n'
