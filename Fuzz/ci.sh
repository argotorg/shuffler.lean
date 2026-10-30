#!/bin/sh
# Usage: Fuzz/ci.sh <build-dir> <seconds> [jobs]
# Fuzzes <build-dir>/fuzz for <seconds> on [jobs] cores (default: all) with the corpus in <build-dir>/corpus.
# Prints each difference and keeps its input in <build-dir>/crashes. A crash without a difference line (a fault in
# the port, solc or the harness) is printed as "crash <tab> FILE". Exit status: 2 if each crash is a difference of
# solc and the model, 1 if there is another crash (a port difference among them), else the status of libFuzzer.
set -u
build=$1 seconds=$2 jobs=${3:-$(nproc)}
mkdir -p "$build/corpus" "$build/crashes"
# with -fork and -ignore_crashes the exit status does not tell if there were crashes
"$build/fuzz" -fork="$jobs" -ignore_crashes=1 -len_control=0 -max_len=512 \
  -max_total_time="$seconds" -artifact_prefix="$build/crashes/" "$build/corpus"
status=$?
crashes=$(find "$build/crashes" -type f)
[ -z "$crashes" ] && exit $status
echo "differences (port, case, port, model) or (solc, case, c++, lean):"
tab=$(printf '\t')
lines=$(for crash in $crashes; do
  line=$("$build/fuzz" "$crash" 2>&1 | grep "$tab")
  echo "${line:-crash$tab$crash}"
done)
echo "$lines"
if echo "$lines" | grep -qv "^solc$tab"; then exit 1; fi
exit 2
