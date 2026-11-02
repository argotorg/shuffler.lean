#!/usr/bin/env bash
# Usage: test/surplus_diff.sh [max] [k]
# Run the "surplus" cases of Fuzz/surplus_cases.sh [max] [k] (default 4 and 2) on the compiled
# remove_surplus of build_bottom_up.S (through build/kraken/c/surplus_harness), the PR31 model
# Shuffler.Emission.removeSurplus (pop_pr31 of the root project, through Fuzz/Oracle.lean), the
# flat model FlatShuffler.Flat.remove_surplus (surplus_flat) and the list model FlatShuffler.Map.State.removeSurplus
# (surplus_flat list), and compare the full results: the status with the blocked offset and
# excess, the stack, the operations and the destination of each slot. Then check that a case
# with a changed destination gives a different result.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cmake -S "$root" -B "$root/build" -G Ninja -DBUILD_TESTING=ON >/dev/null
cmake --build "$root/build" --target shuffler_surplus_harness >/dev/null
(cd "$root" && lake build pop_pr31 >/dev/null)
(cd "$root" && lake build ShufflerKraken/surplus_flat >/dev/null)

run() {
	"$root/build/kraken/c/surplus_harness" < "$1" > "$2/c"
	"$root/.lake/build/bin/pop_pr31" < "$1" > "$2/pr31"
	"$root/kraken/.lake/build/bin/surplus_flat" < "$1" > "$2/flat"
	"$root/kraken/.lake/build/bin/surplus_flat" list < "$1" > "$2/list"
}

sh "$root/Fuzz/surplus_cases.sh" "${1:-4}" "${2:-2}" > "$tmp/cases"
run "$tmp/cases" "$tmp"

for impl in c pr31 flat list; do
	if grep -n -m 5 -e '^invalid' -e '^parse error' -e '^bad input' -e '^err' "$tmp/$impl"; then
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

# Negative: the cases with the destination of each bound slot one up (mod n). Each implementation
# must still agree with the PR31 model, and the results must differ from those of the cases above.
mkdir "$tmp/neg"
awk -F ';' '{
	n = split($3, t, " "); k = split($4, d, " "); out = ""
	for (i = 1; i <= k; i++) out = out (i > 1 ? " " : "") (d[i] == "-" ? "-" : (d[i] + 1) % n)
	print $1 ";" $2 ";" $3 ";" out ";" $5
}' "$tmp/cases" > "$tmp/neg/cases"
run "$tmp/neg/cases" "$tmp/neg"
for impl in c flat list; do
	cmp -s "$tmp/neg/$impl" "$tmp/neg/pr31" || { echo "$impl: differs from pr31 on the changed cases" >&2; exit 1; }
done
if cmp -s "$tmp/neg/pr31" "$tmp/pr31"; then
	echo "the changed cases give the same results" >&2
	exit 1
fi

echo "C++, PR31 model, flat model and list model agree on $(wc -l < "$tmp/cases") cases" \
	"($(grep -c '^ok' "$tmp/c") ok, $(grep -c '^blocked' "$tmp/c") blocked," \
	"$(grep -c 'SWAP' "$tmp/c") with a swap) and on $(wc -l < "$tmp/neg/cases") changed cases"
