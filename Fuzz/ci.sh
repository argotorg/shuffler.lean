#!/bin/sh
# Usage: Fuzz/ci.sh <build-dir> <seconds>
# Fuzzes <build-dir>/fuzz for <seconds> on all cores with the corpus in <build-dir>/corpus. Fails if
# there is a difference, prints it and keeps the input in <build-dir>/crashes.
set -u
build=$1 seconds=$2
mkdir -p "$build/corpus" "$build/crashes"
# with -fork and -ignore_crashes the exit status does not tell if there were crashes
"$build/fuzz" -fork="$(nproc)" -ignore_crashes=1 -len_control=0 -max_len=512 \
  -max_total_time="$seconds" -artifact_prefix="$build/crashes/" "$build/corpus"
status=$?
crashes=$(find "$build/crashes" -type f)
[ -z "$crashes" ] && exit $status
echo "differences (case, c++, lean):"
for crash in $crashes; do "$build/fuzz" "$crash" 2>&1 | grep "$(printf '\t')"; done
exit 1
