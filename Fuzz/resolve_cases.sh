#!/bin/sh
# Usage: Fuzz/resolve_cases.sh
# Prints the "resolve" cases (Fuzz/Oracle.lean) of two sets, each with spillingAllowed 0 and 1 and the dropped byte 0
# for the even and 255 for the odd source offsets:
# - small: at most 2 source and at most 2 target slots, each one of v0 v1 l0 _ R, each injective partial plan, and
#   each working stack of the slots bound for the target offsets below the blocked slot, the blocked slot (with no
#   destination) and the slots bound for the target offsets above it, ascending (each target offset is below, above
#   or absent); the spills {}, {0} and {0, 1}, and the excess 1, 2 and 3.
# - large: 3 source slots, each one of v0 v1 l0 R, and 3 target slots, each one of v0 v1 l0 _, each plan that binds
#   a slot only to an equal slot or a wildcard (as buildMapping does), and the working stack of the blocked slot and
#   the slots bound for all target offsets or all but one, ascending; the spills {} and {0}, and the excess 1, 2 and 4.
set -eu
awk '
function join(a, len,   i, s) {
	s = ""
	for (i = 0; i < len; i++)
		s = s (i ? " " : "") a[i]
	return s
}
# the source slots from offset i up, then the target slots
function sources(i,   k) {
	if (i == m) {
		targets(0)
		return
	}
	for (k = 1; k <= ns; k++) {
		src[i] = sslot[k]
		sources(i + 1)
	}
}
function targets(j,   k, i) {
	if (j == n) {
		for (i = 0; i < m; i++)
			dropped[i] = i % 2 ? 255 : 0
		split("", used)
		plans(0)
		return
	}
	for (k = 1; k <= nt; k++) {
		tgt[j] = tslot[k]
		targets(j + 1)
	}
}
# the destinations of the source slots from offset i up
function plans(i,   d) {
	if (i == m) {
		if (small)
			around(0, "", "")
		else
			above()
		return
	}
	plan[i] = "-"
	plans(i + 1)
	for (d = 0; d < n; d++)
		if (!(d in used) && (small || tgt[d] == src[i] || tgt[d] == "_")) {
			used[d] = 1
			plan[i] = d
			plans(i + 1)
			delete used[d]
		}
}
# small: target offset j and up below the blocked slot, above it or absent
function around(j, below, over,   b) {
	if (j == n) {
		b = split(below, unused, " ")
		cases(below (b ? " " : "") "-" (over == "" ? "" : " " over), b)
		return
	}
	around(j + 1, below, over)
	around(j + 1, below (below == "" ? "" : " ") j, over)
	around(j + 1, below, over (over == "" ? "" : " ") j)
}
# large: all target offsets or all but one above the blocked slot
function above(   skip, j, over) {
	for (skip = -1; skip < n; skip++) {
		over = ""
		for (j = 0; j < n; j++)
			if (j != skip)
				over = over " " j
		cases("-" over, 0)
	}
}
function cases(current, offset,   a, s, e, head) {
	head = join(src, m) ";" join(tgt, n) ";"
	for (a = 0; a <= 1; a++)
		for (s = 1; s <= nspills; s++)
			for (e = 1; e <= nexcess; e++)
				print "resolve;" a ";" head spills[s] ";" join(dropped, m) ";" join(plan, m) ";" current ";" offset " " excess[e]
}
BEGIN {
	small = 1
	ns = split("v0 v1 l0 _ R", sslot, " ")
	nt = split("v0 v1 l0 _ R", tslot, " ")
	nspills = split("|0|0 1", spills, "|")
	nexcess = split("1 2 3", excess, " ")
	for (m = 0; m <= 2; m++)
		for (n = 0; n <= 2; n++)
			sources(0)
	small = 0
	ns = split("v0 v1 l0 R", sslot, " ")
	nt = split("v0 v1 l0 _", tslot, " ")
	nspills = split("|0", spills, "|")
	nexcess = split("1 2 4", excess, " ")
	m = 3
	n = 3
	sources(0)
}'
