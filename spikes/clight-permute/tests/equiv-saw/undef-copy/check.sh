#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../../.." && pwd)
build="$root/build/equiv-saw/undef-copy"
# Build the audited dependencies with build.sh before running this probe.
test -f "$root/build/compcert/cfrontend/ClightBigstep.vo"
mkdir -p "$build"
cp "$root/Permute.v" "$root/Extract.v" "$root/printer.ml" "$root/permute.h" "$build/"
cp "$here/UndefCopy.v" "$here/print_prefixed.ml" "$build/"
cd "$build"
coqc -R "$root/build/compcert" compcert Permute.v > ast.log 2>&1
coqc -R "$root/build/compcert" compcert Extract.v > extraction.log 2>&1
coqc -R "$root/build/compcert" compcert UndefCopy.v > proof.log 2>&1
coqchk -silent -R "$root/build/compcert" compcert -Q . '' UndefCopy > kernel.log 2>&1
ocamlc -w -a -c extracted.mli
ocamlc -w -a -c extracted.ml
ocamlc -c printer.ml
ocamlc -o print-prefixed extracted.cmo printer.cmo print_prefixed.ml
./print-prefixed > prefixed.c
for compiler in gcc clang; do
    "$compiler" -std=c11 -O0 -Werror=uninitialized -c "$root/permute.c" \
        -o "$compiler-baseline.o" > "$compiler-baseline.log" 2>&1
    if "$compiler" -std=c11 -O0 -Werror=uninitialized -c prefixed.c \
        -o "$compiler-prefixed.o" > "$compiler-prefixed.log" 2>&1; then
        printf '%s did not reject the uninitialized read\n' "$compiler" >&2
        exit 1
    fi
    python3 - "$compiler-prefixed.log" <<'PY'
from pathlib import Path
import sys
text = Path(sys.argv[1]).read_text()
assert any("v8" in line and "uninitialized" in line for line in text.splitlines()), text
PY
done
printf 'Clight preserves the call; both C compilers reject its uninitialized read.\n'
