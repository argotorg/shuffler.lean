#!/usr/bin/env bash
# The proof input contains C++ methods only. The tests use the same method bodies.
set -euo pipefail
native=$1
wrappers=$2
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

if awk '/^[[:alpha:]_][[:alnum:]_]*:$/ && !/^_Z/ { found = 1 }
    END { exit !found }' "$native"; then
  echo 'assembly_interfaces_test: a test wrapper is in the proof input' >&2
  exit 1
fi

methods() { sed -n '/^_Z/,/^\s*\.size/p' "$1"; }
methods "$native" > "$tmp/native"
methods "$wrappers" > "$tmp/wrappers"
if [ ! -s "$tmp/native" ] || ! cmp -s "$tmp/native" "$tmp/wrappers"; then
  diff -u "$tmp/native" "$tmp/wrappers" >&2 || true
  echo 'assembly_interfaces_test: the C++ method bodies differ' >&2
  exit 1
fi
echo 'assembly_interfaces_test: the C++ method bodies match'
