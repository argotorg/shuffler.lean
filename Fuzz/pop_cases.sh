#!/bin/sh
# Usage: Fuzz/pop_cases.sh [max]
# Prints each "pop" case (Fuzz/Oracle.lean) with at most [max] (default 5) stack slots and at most [max] target
# slots: each partial injection of the stack offsets into the target offsets, with each number of pops from 0 to one
# more than the stack size. The target slot at offset j is v<j>, a bound slot is the slot of its destination, an
# unbound slot at offset i is l<i>, and each variable is spilled.
set -eu
awk -v max="${1:-5}" '
function emit(m, n, count,   i, stack, target, dests, vars) {
	for (i = 0; i < m; i++) {
		stack = stack (i ? " " : "") (dest[i] == "-" ? "l" i : "v" dest[i])
		dests = dests (i ? " " : "") dest[i]
	}
	for (i = 0; i < n; i++) {
		target = target (i ? " " : "") "v" i
		vars = vars (i ? " " : "") i
	}
	print "pop;" stack ";" target ";" dests ";" vars ";" count
}
# the destinations of the offsets from i up: none, or a target offset that is not used yet
function cases(m, n, i,   j, count) {
	if (i == m) {
		for (count = 0; count <= m + 1; count++)
			emit(m, n, count)
		return
	}
	dest[i] = "-"
	cases(m, n, i + 1)
	for (j = 0; j < n; j++)
		if (!used[j]) {
			used[j] = 1
			dest[i] = j
			cases(m, n, i + 1)
			used[j] = 0
		}
}
BEGIN {
	for (m = 0; m <= max; m++)
		for (n = 0; n <= max; n++)
			cases(m, n, 0)
}'
