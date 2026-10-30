#!/bin/sh
# Usage: Fuzz/surplus_cases.sh [max] [k]
# Prints each "surplus" case (Fuzz/Oracle.lean) of two families. The target slot at offset j is v<j>, a bound slot is
# the slot of its destination, and no variable is spilled.
# Small: at most [max] (default 4) stack slots and at most [max] target slots, each partial injection of the stack
# offsets into the target offsets, and each unbound slot one of v0 v1 l0 _ R (each slot kind, and variables that can
# be equal to a bound slot).
# Deep: 15 to 20 stack slots, so that some slots are out of swap reach, with at most [k] (default 2) unbound slots,
# each l0 or v0. The bound slots go to the target offsets in order from the bottom, or from the top: then the top
# bound slot is v0, equal to each unbound v0.
set -eu
awk -v max="${1:-4}" -v k="${2:-2}" '
function emit(m, n,   i, stack, target, dests) {
	for (i = 0; i < m; i++) {
		stack = stack (i ? " " : "") (dest[i] == "-" ? slot[i] : "v" dest[i])
		dests = dests (i ? " " : "") dest[i]
	}
	for (i = 0; i < n; i++)
		target = target (i ? " " : "") "v" i
	print "surplus;" stack ";" target ";" dests ";"
}
# the small cases: the destinations and unbound slots of the offsets from i up
function small(m, n, i,   j, s) {
	if (i == m) {
		emit(m, n)
		return
	}
	dest[i] = "-"
	for (s = 1; s <= unboundCount; s++) {
		slot[i] = unbound[s]
		small(m, n, i + 1)
	}
	for (j = 0; j < n; j++)
		if (!used[j]) {
			used[j] = 1
			dest[i] = j
			small(m, n, i + 1)
			used[j] = 0
		}
}
# the deep cases: the unbound slots from offset i up, `left` more of them at most
function deep(m, i, left,   s) {
	if (i == m) {
		deepEmit(m)
		return
	}
	dest[i] = "b"
	deep(m, i + 1, left)
	if (left == 0)
		return
	dest[i] = "-"
	for (s = 1; s <= deepCount; s++) {
		slot[i] = deepUnbound[s]
		deep(m, i + 1, left - 1)
	}
}
function deepEmit(m,   i, n, bound, d) {
	n = 0
	for (i = 0; i < m; i++)
		if (dest[i] != "-")
			n++
	for (d = 0; d < 2; d++) {
		bound = 0
		for (i = 0; i < m; i++)
			if (dest[i] != "-")
				dest[i] = d ? n - 1 - bound++ : bound++
		emit(m, n)
	}
	for (i = 0; i < m; i++)
		if (dest[i] != "-")
			dest[i] = "b"
}
BEGIN {
	unboundCount = split("v0 v1 l0 _ R", unbound, " ")
	deepCount = split("l0 v0", deepUnbound, " ")
	for (m = 0; m <= max; m++)
		for (n = 0; n <= max; n++)
			small(m, n, 0)
	for (m = 15; m <= 20; m++)
		deep(m, 0, k)
}'
