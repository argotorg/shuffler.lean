#!/bin/sh
# SPDX-License-Identifier: GPL-3.0-or-later
set -eu
test_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=${1:-"$test_dir/../build/guided"}
build_dir=$(CDPATH= cd -- "$build_dir" && pwd)
corpus_dir=${2:-"$build_dir/corpus"}
report=$(mktemp -d "$build_dir/report.XXXXXX")
mkdir "$report/corpus"
python3 - "$corpus_dir" "$report/corpus" <<'PY'
import hashlib
from pathlib import Path
import re
import sys

source, target = map(Path, sys.argv[1:])
for path in sorted(source.iterdir()):
    try:
        if not path.is_file():
            continue
        before = path.stat()
        data = path.read_bytes()
        after = path.stat()
    except FileNotFoundError:
        continue  # libFuzzer can remove a reduced input during the snapshot.
    if (before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_ino, after.st_size, after.st_mtime_ns):
        continue  # AFL++ can trim a queued input during the snapshot.
    if re.fullmatch(r"[0-9a-f]{40}", path.name) and hashlib.sha1(data).hexdigest() != path.name:
        continue  # A newly created input has not yet been written in full.
    (target / path.name).write_bytes(data)
if not any(target.iterdir()):
    sys.exit("coverage snapshot has no inputs")
PY
LLVM_PROFILE_FILE="$report/run.profraw" "$build_dir/coverage/permute-fuzz" \
    -runs=0 "$report/corpus" > "$report/replay.log" 2>&1
llvm-profdata merge -sparse "$report/run.profraw" -o "$report/run.profdata"
core=$(CDPATH= cd -- "$test_dir/.." && pwd)/permute.c
oracle="$build_dir/oracle/solc_permute.inc"
llvm-cov export "$build_dir/coverage/permute-fuzz" -instr-profile="$report/run.profdata" \
    "$core" "$oracle" > "$report/coverage.json"
llvm-cov report "$build_dir/coverage/permute-fuzz" -instr-profile="$report/run.profdata" \
    "$core" "$oracle" > "$report/summary.txt"
llvm-cov show "$build_dir/coverage/permute-fuzz" -instr-profile="$report/run.profdata" \
    -show-branches=count -show-expansions -format=html -output-dir="$report/html" "$core" "$oracle"
python3 "$test_dir/coverage-report.py" "$report/coverage.json" "$core" "$oracle" \
    > "$report/branches.txt"
cat "$report/summary.txt" "$report/branches.txt"
printf 'Coverage snapshot: %s\n' "$report"
