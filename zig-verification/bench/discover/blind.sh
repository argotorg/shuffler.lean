#!/usr/bin/env bash
# The blindness check of the invariant discovery (docs/research/invariant-discovery-design-20261119.md, 4.2).
#   bench/discover/blind.sh [PATH ...]
# Greps PATH (files or directories) for the whole words of bench/discover/forbidden.txt (one word for each line). With no
# PATH it checks Skel/Discover and Skel/Test/Discover*. BLIND_WORDS sets another word file.
# Exit 0: no word found. Exit 1: a word found (the lines are printed). Exit 2: an error (no word file, no word in it, a path
# that does not exist, a grep failure or an invalid source boundary); an error is never a pass.
# Target adapters may name machine code. The boundary check rejects producer references to an adapter
# and denied hand-proof references in all sources checked here, including the adapters.
set -u
root="$(cd "$(dirname "$0")/../.." && pwd)"
words="${BLIND_WORDS:-$root/bench/discover/forbidden.txt}"
if [ ! -r "$words" ] || ! grep -q '[^[:space:]]' "$words"; then
  echo "blind: no word in $words" >&2
  exit 2
fi
if [ $# -eq 0 ]; then
  set -- "$root/Skel/Discover" "$root"/Skel/Test/Discover*
fi
for p in "$@"; do
  if [ ! -e "$p" ]; then
    echo "blind: no such path: $p" >&2
    exit 2
  fi
done
# Check denied paths before grep can read them.
python3 "$root/bench/discover/boundary.py" "$root" "${BLIND_PRODUCER_ROOT:-$root/Skel/Discover}" \
  "$@" "$root/Skel/Targets" "$root/Skel/Test/FullRegions.lean"
case $? in
  0) ;;
  1) exit 1 ;;
  *) exit 2 ;;
esac
grep -rnwF -f <(grep '[^[:space:]]' "$words") -- "$@"
case $? in
  0) echo "blind: a forbidden word is in the code" >&2; exit 1 ;;
  1) exit 0 ;;
  *) echo "blind: grep failed" >&2; exit 2 ;;
esac
