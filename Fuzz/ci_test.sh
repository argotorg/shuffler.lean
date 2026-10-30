#!/bin/sh
# Tests the exit status of Fuzz/ci.sh with a fake fuzz program: the fuzz run does nothing, and the replay of a
# crash file prints its text. Usage: Fuzz/ci_test.sh
set -u
ci=$(dirname "$0")/ci.sh
tab=$(printf '\t')
failures=0
# expect STATUS CRASH... : ci.sh exits with STATUS when the crash files have the texts CRASH...
expect() {
  want=$1; shift
  build=$(mktemp -d)
  printf '#!/bin/sh\ncase $1 in -fork=*) exit 0;; *) cat "$1";; esac\n' > "$build/fuzz"
  chmod +x "$build/fuzz"
  mkdir -p "$build/crashes"
  i=0
  for text in "$@"; do i=$((i + 1)); printf '%s\n' "$text" > "$build/crashes/crash-$i"; done
  sh "$ci" "$build" 1 1 > "$build/out" 2>&1
  got=$?
  if [ "$got" != "$want" ]; then
    echo "FAIL: crashes [$*]: exit $got, not $want"; cat "$build/out"; failures=$((failures + 1))
  fi
  rm -r "$build"
}
expect 0
expect 2 "solc${tab}case${tab}c++${tab}lean"
expect 2 "solc${tab}a${tab}b${tab}c" "solc${tab}d${tab}e${tab}f"
expect 1 "port${tab}case${tab}port${tab}model"
expect 1 "solc${tab}a${tab}b${tab}c" "port${tab}d${tab}e${tab}f"
# a crash without a difference line, alone and after a solc difference
expect 1 "segfault"
expect 1 "solc${tab}a${tab}b${tab}c" ""
[ "$failures" = 0 ] && echo "ci_test: all checks pass" || { echo "$failures failures"; exit 1; }
