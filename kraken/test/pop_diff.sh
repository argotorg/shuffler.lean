#!/usr/bin/env bash
# Usage: test/pop_diff.sh [max]
# Run the "pop" cases of Fuzz/pop_cases.sh [max] (default 5) on the compiled emission_pop of
# build_bottom_up.S (through build/kraken/c/pop_harness), the PR31 model Shuffler.Emission.State.pop
# (pop_pr31 of the root project, through Fuzz/Oracle.lean), the flat model
# FlatShuffler.Flat.emission_pop (pop_flat) and the list model FlatShuffler.Map.State.pops (pop_flat list), and
# compare the full results: the status, the stack, the operations, the destination of each slot,
# the position of each target offset and the pending count.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cmake -S "$root" -B "$root/build" -G Ninja -DBUILD_TESTING=ON >/dev/null
cmake --build "$root/build" --target shuffler_pop_harness >/dev/null
(cd "$root" && lake build pop_pr31 >/dev/null)
(cd "$root" && lake build ShufflerKraken/pop_flat >/dev/null)

sh "$root/Fuzz/pop_cases.sh" "${1:-5}" > "$tmp/cases"
"$root/build/kraken/c/pop_harness" < "$tmp/cases" > "$tmp/c"
"$root/.lake/build/bin/pop_pr31" < "$tmp/cases" > "$tmp/pr31"
"$root/kraken/.lake/build/bin/pop_flat" < "$tmp/cases" > "$tmp/flat"
"$root/kraken/.lake/build/bin/pop_flat" list < "$tmp/cases" > "$tmp/list"

for impl in c pr31 flat list; do
	if grep -n -m 5 -e '^invalid' -e '^parse error' -e '^bad input' "$tmp/$impl"; then
		echo "$impl: lines that must not occur" >&2
		exit 1
	fi
done
for impl in c flat list; do
	if ! cmp "$tmp/$impl" "$tmp/pr31"; then
		paste -d '\n' "$tmp/cases" "$tmp/pr31" "$tmp/$impl" /dev/null \
			| awk -v impl="$impl" 'NR % 4 == 2 { o = $0 } NR % 4 == 3 && $0 != o { print s; print "pr31 " o; print impl " " $0; if (++k == 3) exit } NR % 4 == 1 { s = $0 }'
		exit 1
	fi
done
echo "C++, PR31 model, flat model and list model agree on $(wc -l < "$tmp/cases") cases ($(grep -c '^ok' "$tmp/c") ok, $(grep -c '^err' "$tmp/c") err)"
