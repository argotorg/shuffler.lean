#!/usr/bin/env bash
# Usage: test/lowest_diff.sh [max]
# Run the "lowest" cases of Fuzz/lowest_cases.sh [max] (default 4) on the compiled
# permute_at_lowest_height of build_bottom_up.S (through build/kraken/c/lowest_harness), the PR31 model
# Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight (lowest_pr31 of the root project, through
# Fuzz/Oracle.lean), the flat model FlatShuffler.Flat.permute_at_lowest_height (lowest_flat) and the list
# model FlatShuffler.lowest (lowest_flat list), and compare the full results: the status with the blocked
# offset and excess, the stack, the operations and the destination of each slot. The list model has
# no unbound slot: it prints "unbound" for a case with a destination "-", and the script does not
# compare these lines. Then check that a case with changed destinations gives a different result.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cmake -S "$root" -B "$root/build" -G Ninja -DBUILD_TESTING=ON >/dev/null
cmake --build "$root/build" --target shuffler_lowest_harness >/dev/null
(cd "$root" && lake build lowest_pr31 >/dev/null)
(cd "$root" && lake build ShufflerKraken/lowest_flat >/dev/null)

run() {
	"$root/build/kraken/c/lowest_harness" < "$1" > "$2/c"
	"$root/.lake/build/bin/lowest_pr31" < "$1" > "$2/pr31"
	"$root/kraken/.lake/build/bin/lowest_flat" < "$1" > "$2/flat"
	"$root/kraken/.lake/build/bin/lowest_flat" list < "$1" > "$2/list"
}

# The first differences of $2 from $1 (pr31) on the cases $3, if the result of $2 is not "unbound".
show() {
	paste -d '\n' "$3" "$1" "$2" /dev/null \
		| awk -v impl="$(basename "$2")" 'NR % 4 == 2 { o = $0 } NR % 4 == 3 && $0 != o && $0 != "unbound" { print s; print "pr31 " o; print impl " " $0; if (++k == 3) exit } NR % 4 == 1 { s = $0 }'
}

# The cases $1 agree on: c, flat and list are the same as pr31 (list only where it is not
# "unbound"), and list is "unbound" only where a destination is "-".
check() {
	for impl in c pr31 flat list; do
		if grep -n -m 5 -e '^invalid' -e '^parse error' -e '^bad input' "$1/$impl"; then
			echo "$impl: lines that must not occur" >&2
			return 1
		fi
	done
	for impl in c flat; do
		if ! cmp -s "$1/$impl" "$1/pr31"; then
			show "$1/pr31" "$1/$impl" "$1/cases"
			return 1
		fi
	done
	if [ -n "$(show "$1/pr31" "$1/list" "$1/cases")" ]; then
		show "$1/pr31" "$1/list" "$1/cases"
		return 1
	fi
	if ! paste -d ";" "$1/cases" "$1/list" \
		| awk -F ";" '($6 == "unbound") != ($4 ~ /-/) { print; bad = 1 } END { exit bad }'; then
		echo "list: \"unbound\" does not match the cases with a destination \"-\"" >&2
		return 1
	fi
}

mkdir "$tmp/base"
sh "$root/Fuzz/lowest_cases.sh" "${1:-4}" > "$tmp/base/cases"
run "$tmp/base/cases" "$tmp/base"
check "$tmp/base"

# Negative: the cases with the destination of each bound slot one up (mod n). Each implementation
# must still agree with the PR31 model, and the results must differ from those of the cases above.
mkdir "$tmp/neg"
awk -F ';' '{
	n = split($3, t, " "); k = split($4, d, " "); out = ""
	for (i = 1; i <= k; i++) out = out (i > 1 ? " " : "") (d[i] == "-" ? "-" : (d[i] + 1) % n)
	print $1 ";" $2 ";" $3 ";" out ";" $5
}' "$tmp/base/cases" > "$tmp/neg/cases"
run "$tmp/neg/cases" "$tmp/neg"
check "$tmp/neg"
if cmp -s "$tmp/neg/pr31" "$tmp/base/pr31"; then
	echo "the changed cases give the same results" >&2
	exit 1
fi

b=$tmp/base
echo "C++, PR31 model, flat model and list model agree on $(wc -l < "$b/cases") cases" \
	"($(grep -c '^ok' "$b/c") ok, $(grep -c '^blocked' "$b/c") blocked, $(grep -c '^err' "$b/c") err," \
	"$(grep -c 'SWAP' "$b/c") with a swap; the list model on the $(grep -vc '^unbound' "$b/list")" \
	"cases with no destination \"-\") and on $(wc -l < "$tmp/neg/cases") changed cases"
