# Renames the labels .LB<N> of the sed step to .LB.NAME.K. K counts the labels of one function
# from 0, in the order of their lines. NAME is the function name; for a g++ (Itanium) name it is the
# nested names without the anonymous namespace, joined with ".": Emission.permute for
# _ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE. gcc numbers the labels
# across the file, so a new function changes the numbers of the functions after it; the new names
# depend only on their own function. A function is the lines from "NAME:" to its .size line.
# Fails if two functions get the same NAME, or for a .LB<N> that is not a label of its function.

function fail(message) {
	print "labels.awk: line " NR ": " message > "/dev/stderr"
	failed = 1
	exit 1
}

function prefix(symbol,    s, name, n, out) {
	if (symbol !~ /^_Z/)
		return symbol
	s = symbol
	sub(/^_ZN?K?/, "", s)
	out = ""
	while (match(s, /^[1-9][0-9]*/)) {
		n = substr(s, 1, RLENGTH) + 0
		name = substr(s, RLENGTH + 1, n)
		s = substr(s, RLENGTH + 1 + n)
		if (name != "_GLOBAL__N_1")
			out = out (out == "" ? "" : ".") name
	}
	if (out == "")
		fail("no name for " symbol)
	return out
}

# Prints the lines of the function with the new names.
function flush(    i, s, out, label) {
	for (i = 1; i <= n; i++) {
		s = line[i]
		out = ""
		while (match(s, /\.LB[0-9]+/)) {
			label = substr(s, RSTART, RLENGTH)
			if (!(label in to))
				fail(label " is not a label of " function_)
			out = out substr(s, 1, RSTART - 1) to[label]
			s = substr(s, RSTART + RLENGTH)
		}
		print out s
	}
	delete to
	function_ = ""
}

/^[a-zA-Z_][a-zA-Z0-9_]*:$/ {
	function_ = substr($0, 1, length($0) - 1)
	name = prefix(function_)
	if (name in owner)
		fail(owner[name] " and " function_ " have the name " name)
	owner[name] = function_
	n = k = 0
}

function_ != "" {
	line[++n] = $0
	if ($0 ~ /^\.LB[0-9]+:$/)
		to[substr($0, 1, length($0) - 1)] = ".LB." name "." k++
	if ($0 ~ /^\t\.size\t/)
		flush()
	next
}

/\.LB[0-9]/ { fail(".LB label outside a function") }

{ print }

END {
	if (failed)
		exit 1
	if (function_ != "")
		fail("no .size line for " function_)
}
