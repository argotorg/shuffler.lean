#!/bin/sh
# Usage: Fuzz/map_cases.sh [max]
# Prints each "map" case (Fuzz/Oracle.lean) with at most [max] (default 3) source slots and at most [max] target slots,
# each one of v0 v1 l0 _ R (each slot kind, and two variables, so that some slots have a copy and some do not), each
# source slot dropped (1) or not (0), for both strategies.
set -eu
awk -v max="${1:-3}" '
# the source slots and dropped bytes from offset i up
function sources(m, i, source, dropped,   s, d) {
	if (i == m) {
		targets(source, dropped)
		return
	}
	for (s = 1; s <= n; s++)
		for (d = 0; d <= 1; d++)
			sources(m, i + 1, source (i ? " " : "") slot[s], dropped (i ? " " : "") d)
}
function targets(source, dropped,   len) {
	for (len = 0; len <= max; len++)
		target(source, dropped, len, 0, "")
}
# the target slots from offset i up
function target(source, dropped, len, i, slots,   s) {
	if (i == len) {
		print "map;L;" source ";" slots ";" dropped
		print "map;T;" source ";" slots ";" dropped
		return
	}
	for (s = 1; s <= n; s++)
		target(source, dropped, len, i + 1, slots (i ? " " : "") slot[s])
}
BEGIN {
	n = split("v0 v1 l0 _ R", slot, " ")
	for (m = 0; m <= max; m++)
		sources(m, 0, "", "")
}'
