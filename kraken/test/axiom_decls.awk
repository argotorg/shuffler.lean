# Print FILE:LINE: TEXT for each `axiom` declaration in the Lean files given as input.
# Comments (`--` and nested `/- -/`) and string literals are removed first, so a
# comment that starts a line with the word "axiom" is not a match.
FNR == 1 { depth = 0 }
{
	out = ""
	n = length($0)
	for (i = 1; i <= n; i++) {
		c = substr($0, i, 1); c2 = substr($0, i, 2)
		if (depth > 0) {
			if (c2 == "/-") { depth++; i++ }
			else if (c2 == "-/") { depth--; i++ }
		} else if (c2 == "--") {
			break
		} else if (c2 == "/-") {
			depth = 1; i++
		} else if (c == "\"") {
			for (i++; i <= n && substr($0, i, 1) != "\""; i++)
				if (substr($0, i, 1) == "\\") i++
			out = out "\"\""
		} else {
			out = out c
		}
	}
	if (out ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|public|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]/)
		print FILENAME ":" FNR ": " $0
}
