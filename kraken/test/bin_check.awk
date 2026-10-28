# Compare a Kraken program with a disassembly (see test/bin_check.sh).
#
#   awk -f test/bin_check.awk HOST DIS
#
# HOST has one line "ADDR SIZE TEXT" for each directive (test/BinHostMain.lean).
# DIS has "start ADDR", "stop ADDR", then one line "ADDR SIZE KIND TEXT" for each
# instruction (test/bin_objdump.sh). ADDR is hex. Each instruction must have the same
# address, size and text. The texts are put in one normal form first, with these
# rules. Each rule is trusted.
#
#   W  (both)    Runs of blanks become one space, and the space after a comma goes.
#   C  (objdump) The symbol comment "<sym+off>" after a branch target goes.
#   S  (objdump) The suffix "q" goes from call, ret, jmp, lea and cmovCC. Kraken
#                prints these without a suffix: the width is 64, or the register
#                operand gives it.
#   X  (objdump) movzSD and movsSD with a register source become movzx and movsx, as
#                Kraken prints them. The register names give the widths.
#   N  (objdump) Hex numbers become decimal. A displacement keeps its sign, and a
#                zero displacement goes (Kraken does not print it). An immediate is a
#                two's complement number with the width of the mnemonic suffix
#                (b, w, l, q; else 64), as gcc writes it in the .S file.
#   L  (Kraken)  A branch or call target label becomes its address in HOST.
#   P  (size)    The alignment nops after an instruction (KIND "pad") count in the
#                size of that instruction. The Kraken parser drops `.p2align`, so the
#                padding has no directive of its own.

function fail(msg) { print "bin_check: " msg > "/dev/stderr"; failed = 1; exit 1 }
function hex(n) { return sprintf("%x", n) }
function digit(c) { return index("0123456789abcdef", c) - 1 }
# The hex digits h as a two's complement number of w bits (w = 0: no sign bit).
function signed(h, w,   n, i) {
	n = 0
	if (length(h) == w / 4 && digit(substr(h, 1, 1)) >= 8) {
		for (i = 1; i <= length(h); i++) n = n * 16 + 15 - digit(substr(h, i, 1))
		n = -(n + 1)
	} else
		for (i = 1; i <= length(h); i++) n = n * 16 + digit(substr(h, i, 1))
	if (n >= 2 ^ 53 || n <= -2 ^ 53) fail("number too large: 0x" h)
	return n
}
# Rule W.
function blanks(t) {
	gsub(/[ \t]+/, " ", t); gsub(/, /, ",", t); sub(/^ /, "", t); sub(/ $/, "", t)
	return t
}
function norm_objdump(t,   m, ops, s, w, out, h) {
	sub(/ <[^>]*>[ \t]*$/, "", t)  # Rule C.
	t = blanks(t)
	m = t; sub(/ .*/, "", m)
	ops = substr(t, length(m) + 2)
	if (m ~ /^(call|ret|jmp|lea|cmov[a-z]+)q$/) m = substr(m, 1, length(m) - 1)  # Rule S.
	if (m ~ /^mov[sz][bwl][wlq]$/ && ops ~ /^%/) m = substr(m, 1, 4) "x"  # Rule X.
	# Rule N.
	s = substr(m, length(m))
	w = s == "b" ? 8 : s == "w" ? 16 : s == "l" ? 32 : 64
	out = ""
	while (match(ops, /\$0x[0-9a-f]+|-?0x[0-9a-f]+\(/)) {
		h = substr(ops, RSTART, RLENGTH)
		if (h ~ /^\$/) h = "$" signed(substr(h, 4), w)
		else if (h ~ /^-/) h = "-" signed(substr(h, 4, length(h) - 4), 0) "("
		else h = signed(substr(h, 3, length(h) - 3), 0) "("
		if (h == "0(") h = "("
		out = out substr(ops, 1, RSTART - 1) h
		ops = substr(ops, RSTART + RLENGTH)
	}
	ops = out ops
	return ops == "" ? m : m " " ops
}
function norm_kraken(t,   m, ops) {
	t = blanks(t)
	m = t; sub(/ .*/, "", m)
	ops = substr(t, length(m) + 2)
	# Rule L.
	if (m ~ /^(j[a-z]+|call)$/ && ops !~ /^[%*]/) {
		if (!(ops in lab)) fail("unknown label " ops)
		ops = hex(lab[ops])
	}
	return ops == "" ? m : m " " ops
}

BEGIN { nh = 0; no = 0; nlab = 0 }
FNR == 1 { file++ }
file == 1 {
	text = $0; sub(/^[^ ]+ [^ ]+ /, "", text)
	if (text ~ /:$/) { lab[substr(text, 1, length(text) - 1)] = strtonum("0x" $1); nlab++; next }
	ha[nh] = strtonum("0x" $1); hs[nh] = $2 + 0; ht[nh] = text; nh++
	next
}
$1 == "start" { start = strtonum("0x" $2); next }
$1 == "stop" { stop = strtonum("0x" $2); next }
{
	oa[no] = strtonum("0x" $1); os[no] = $2 + 0; ok[no] = $3
	text = $0; sub(/^[^ ]+ [^ ]+ [^ ]+ /, "", text); ot[no] = text; no++
}
END {
	if (failed) exit 1
	if (nh == 0 || ha[0] != start) fail("the program does not start at " hex(start))
	j = 0; pad = 0
	for (k = 0; k < nh; k++) {
		if (j >= no) fail("the binary has no instruction at " hex(ha[k]) ": " ht[k])
		if (ok[j] != "instr") fail("padding at " hex(oa[j]) " where Kraken has " ht[k])
		if (oa[j] != ha[k])
			fail("address " hex(ha[k]) " in Kraken, " hex(oa[j]) " in the binary: " ht[k])
		a = norm_kraken(ht[k]); b = norm_objdump(ot[j])
		if (a != b) fail("at " hex(ha[k]) ": Kraken \"" a "\", binary \"" b "\"")
		size = os[j]; j++
		# Rule P.
		while (j < no && ok[j] == "pad") { size += os[j]; pad += os[j]; j++ }
		if (size != hs[k])
			fail("at " hex(ha[k]) ": size " hs[k] " in Kraken, " size " in the binary")
	}
	if (j != no) fail("the binary has more code at " hex(oa[j]) ": " ot[j])
	if (ha[nh - 1] + hs[nh - 1] != stop) fail("the program does not end at " hex(stop))
	printf "bin_check: %d instructions match (%d labels, %d padding bytes), %s to %s\n", \
		nh, nlab, pad, hex(start), hex(stop)
}
