#!/bin/sh
# Usage: Fuzz/plan_cases.sh [max]
# Prints each "plan" case (Fuzz/Oracle.lean) with at most [max] (default 2) source slots and at most [max] target
# slots, each one of v0 v1 l0 _ R (each slot kind, and two variables, so that some slots have a copy and some do not),
# for both strategies, both values of spillingAllowed, and each set of spilled variables of v0 v1.
set -eu
awk -v max="${1:-2}" '
# the slots of a stack of len slots from offset i up, each one passed to f
function stacks(f, len, i, slots, prefix,   s, t) {
	if (i == len) {
		if (f == "source")
			for (t = 0; t <= max; t++)
				stacks("target", t, 0, "", slots)
		else
			emit(prefix, slots)
		return
	}
	for (s = 1; s <= n; s++)
		stacks(f, len, i + 1, slots (i ? " " : "") slot[s], prefix)
}
function emit(source, target,   st, b, v) {
	for (st = 1; st <= 2; st++)
		for (b = 0; b <= 1; b++)
			for (v = 1; v <= 4; v++)
				print "plan;" strategy[st] ";" b ";" source ";" target ";" vars[v]
}
BEGIN {
	n = split("v0 v1 l0 _ R", slot, " ")
	split("L T", strategy, " ")
	vars[1] = ""; vars[2] = "0"; vars[3] = "1"; vars[4] = "0 1"
	for (m = 0; m <= max; m++)
		stacks("source", m, 0, "", "")
}'
