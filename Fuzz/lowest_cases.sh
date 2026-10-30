#!/bin/sh
# Usage: Fuzz/lowest_cases.sh [max]
# Prints each "lowest" case (Fuzz/Oracle.lean) of two families. A bound slot is the target slot of its destination, an
# unbound slot is l9, and no variable is spilled.
# Small: at most [max] (default 4) stack slots and at most [max] target slots, each target slot one of v0 v1 l0 (so
# that some slots are equal), and each partial injection of the stack offsets into the target offsets (a slot without
# a destination is an error).
# Deep: 15 to 20 stack slots, so that some swaps are out of reach, and 2 target slots more, v0 v1 ... Each slot goes
# to its own offset, but two slots p < q, which go to two distinct offsets of p, q and the two offsets above the
# stack. Then a slot can be parked (its destination is above the stack), and an offset of p or q can be a hole (no
# slot is bound for it).
set -eu
awk -v max="${1:-4}" '
function emit(m, n,   i, stack, target, dests, line) {
	for (i = 0; i < m; i++) {
		stack = stack (i ? " " : "") (dest[i] == "-" ? "l9" : tslot[dest[i]])
		dests = dests (i ? " " : "") dest[i]
	}
	for (i = 0; i < n; i++)
		target = target (i ? " " : "") tslot[i]
	line = "lowest;" stack ";" target ";" dests ";"
	# the deep family makes some cases more than once
	if (!(line in seen))
		print line
	seen[line] = 1
}
# the small cases: the target slots from offset j up, then the destinations
function targets(m, n, j,   s) {
	if (j == n) {
		small(m, n, 0)
		return
	}
	for (s = 1; s <= kindCount; s++) {
		tslot[j] = kinds[s]
		targets(m, n, j + 1)
	}
}
# the destinations of the stack offsets from i up
function small(m, n, i,   j) {
	if (i == m) {
		emit(m, n)
		return
	}
	dest[i] = "-"
	small(m, n, i + 1)
	for (j = 0; j < n; j++)
		if (!used[j]) {
			used[j] = 1
			dest[i] = j
			small(m, n, i + 1)
			used[j] = 0
		}
}
BEGIN {
	kindCount = split("v0 v1 l0", kinds, " ")
	for (m = 0; m <= max; m++)
		for (n = 0; n <= max; n++)
			targets(m, n, 0)
	for (m = 15; m <= 20; m++) {
		n = m + 2
		for (j = 0; j < n; j++)
			tslot[j] = "v" j
		for (p = 0; p < m; p++)
			for (q = p + 1; q < m; q++) {
				for (i = 0; i < m; i++)
					dest[i] = i
				split(p " " q " " m " " m + 1, offsets, " ")
				for (a = 1; a <= 4; a++)
					for (b = 1; b <= 4; b++)
						if (a != b) {
							dest[p] = offsets[a]
							dest[q] = offsets[b]
							emit(m, n)
						}
			}
	}
}'
