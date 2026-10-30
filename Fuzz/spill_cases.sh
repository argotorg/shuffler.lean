#!/bin/sh
# Usage: Fuzz/spill_cases.sh [max]
# Prints each "spill" case (Fuzz/Oracle.lean) with at most [max] (default 4) adds, each one of the slots
# v0 v1 v2 l0 l1 l2 _ R: once with no queries, and once with the queries v0 v1 v2 v3 l0 l1 l2 _ R (each slot kind, the
# variable v3 that no case adds, and a literal with the payload of each added variable).
set -eu
awk -v max="${1:-4}" '
# the adds from offset i up, after the adds `adds`
function cases(len, i, adds,   k) {
	if (i == len) {
		print "spill;" adds ";"
		print "spill;" adds ";" queries
		return
	}
	for (k = 1; k <= n; k++)
		cases(len, i + 1, adds (i ? " " : "") slot[k])
}
BEGIN {
	n = split("v0 v1 v2 l0 l1 l2 _ R", slot, " ")
	queries = "v0 v1 v2 v3 l0 l1 l2 _ R"
	for (len = 0; len <= max; len++)
		cases(len, 0, "")
}'
