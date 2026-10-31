#!/usr/bin/env bash
# Usage: test/plan_diff.sh [max] [count] [seed]
# Run the "plan" cases of Fuzz/plan_cases.sh [max] (default 3) and [count] (default 20000) random
# "plan" cases from [seed] (default 1) on the PR31 model Shuffler.Planner.run (lowest_pr31 of the
# root project, through Fuzz/Oracle.lean) and the flat model Bbu.Flat.planEntry (plan_flat), and
# compare the full results: the success, the spills, the dropped slots, the stack, the operations
# and the source of each target slot. Then check that the cases with the other strategy agree too
# and give different results. Run it with nice.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

(cd "$root" && lake build lowest_pr31 >/dev/null)
(cd "$root/kraken" && lake build plan_flat >/dev/null)

run() {
	"$root/.lake/build/bin/lowest_pr31" < "$1" > "$2/pr31"
	"$root/kraken/.lake/build/bin/plan_flat" < "$1" > "$2/flat"
}

check() {
	if grep -n -m 5 -e '^invalid' -e '^parse error' -e '^bad input' "$1/pr31" "$1/flat"; then
		echo "lines that must not occur" >&2
		exit 1
	fi
	if ! cmp "$1/flat" "$1/pr31"; then
		paste -d '\n' "$1/cases" "$1/pr31" "$1/flat" /dev/null \
			| awk 'NR % 4 == 2 { o = $0 } NR % 4 == 3 && $0 != o { print s; print "pr31 " o; print "flat " $0; if (++k == 3) exit } NR % 4 == 1 { s = $0 }'
		exit 1
	fi
}

sh "$root/Fuzz/plan_cases.sh" "${1:-3}" > "$tmp/cases"
# Random cases with at most 40 slots in each stack. A target slot is a copy of a source slot with
# probability 0.8. Each variable below the variable count k is spilled with probability 0.2.
awk -v seed="${3:-1}" -v count="${2:-20000}" -v max=40 '
function slot(k,   r) {
	r = rand()
	if (r < 0.75) return "v" int(rand() * k)
	if (r < 0.83) return "l" int(rand() * 3)
	if (r < 0.98) return "_"
	return "R"
}
function stack(len, k, src,   i, s, n, a) {
	n = split(src, a, " ")
	s = ""
	for (i = 0; i < len; i++) s = s (i ? " " : "") (n && rand() < 0.8 ? a[1 + int(rand() * n)] : slot(k))
	return s
}
BEGIN {
	srand(seed)
	for (c = 0; c < count; c++) {
		k = 1 + int(rand() * max)
		v = ""
		for (i = 0; i < k; i++) if (rand() < 0.2) v = v (v == "" ? "" : " ") i
		s = stack(int(rand() * (max + 1)), k, "")
		print "plan;" (rand() < 0.5 ? "L" : "T") ";" int(rand() * 2) ";" s ";" stack(int(rand() * (max + 1)), k, s) ";" v
	}
}' >> "$tmp/cases"
run "$tmp/cases" "$tmp"
check "$tmp"

# Negative: the cases with the other strategy. The models must still agree, and the results must
# differ from those of the cases above.
mkdir "$tmp/neg"
awk -F ';' -v OFS=';' '{ $2 = $2 == "L" ? "T" : "L"; print }' "$tmp/cases" > "$tmp/neg/cases"
run "$tmp/neg/cases" "$tmp/neg"
check "$tmp/neg"
if cmp -s "$tmp/neg/pr31" "$tmp/pr31"; then
	echo "the changed cases give the same results" >&2
	exit 1
fi

echo "PR31 model and flat model agree on $(wc -l < "$tmp/cases") cases" \
	"($(grep -c '^err' "$tmp/pr31") err, $(grep -c '^ok 0' "$tmp/pr31") stuck," \
	"$(grep -c '^ok 1' "$tmp/pr31") ok, $(grep -c '^ok [01];[01];[^;]*;[^;]*1' "$tmp/pr31") with a drop)" \
	"and on $(wc -l < "$tmp/neg/cases") changed cases"
