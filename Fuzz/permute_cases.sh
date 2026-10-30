#!/bin/sh
# Usage: Fuzz/permute_cases.sh [max]
# Prints each "permute" case (Fuzz/Oracle.lean) of two families. The destinations are a permutation of the offsets.
# Small: at most [max] (default 4) slots, each slot one of v0 v1 l0 _ R (each slot kind, with equal slots in groups),
# and each permutation.
# Deep: 15 to 20 slots, so that some slots are out of swap reach. The slot at offset i is v<i> (all distinct), or
# v<i mod 2> (two groups). The permutations are the identity, each exchange of two offsets, each rotation and the
# reversal.
set -eu
awk -v max="${1:-4}" '
function emit(h,   i, stack, dests) {
	for (i = 0; i < h; i++) {
		stack = stack (i ? " " : "") slot[i]
		dests = dests (i ? " " : "") dest[i]
	}
	print "permute;" stack ";" dests
}
# the small cases: the slots of the offsets from i up
function slots(h, i,   s) {
	if (i == h) {
		perms(h, 0)
		return
	}
	for (s = 1; s <= kinds; s++) {
		slot[i] = kind[s]
		slots(h, i + 1)
	}
}
# the destinations of the offsets from i up
function perms(h, i,   j) {
	if (i == h) {
		emit(h)
		return
	}
	for (j = 0; j < h; j++)
		if (!used[j]) {
			used[j] = 1
			dest[i] = j
			perms(h, i + 1)
			used[j] = 0
		}
}
function deep(h,   i, j, r) {
	for (i = 0; i < h; i++)
		dest[i] = i
	emit(h)
	for (i = 0; i < h; i++)
		for (j = i + 1; j < h; j++) {
			dest[i] = j
			dest[j] = i
			emit(h)
			dest[i] = i
			dest[j] = j
		}
	for (r = 1; r < h; r++) {
		for (i = 0; i < h; i++)
			dest[i] = (i + r) % h
		emit(h)
	}
	for (i = 0; i < h; i++)
		dest[i] = h - 1 - i
	emit(h)
}
BEGIN {
	kinds = split("v0 v1 l0 _ R", kind, " ")
	for (h = 0; h <= max; h++)
		slots(h, 0)
	for (h = 15; h <= 20; h++) {
		for (i = 0; i < h; i++)
			slot[i] = "v" i
		deep(h)
		for (i = 0; i < h; i++)
			slot[i] = "v" (i % 2)
		deep(h)
	}
}'
