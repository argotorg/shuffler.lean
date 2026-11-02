#!/usr/bin/env bash
# Test c/labels.awk: a label name depends only on its own function, and the object code does
# not change.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
awkf=$dir/c/labels.awk
asm=$dir/../build/kraken/c/build_bottom_up.S
cmake -S "$dir/.." -B "$dir/../build" -G Ninja >/dev/null
cmake --build "$dir/../build" --target shuffler_assembly >/dev/null
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fails=0
fail() { echo "FAIL $1"; fails=$((fails + 1)); }

# gcc SEED < FILE: the labels .LB.NAME.K of FILE as gcc numbers them after the sed step
# (.LB<N>), with N a random permutation of 1..count.
gcc() {
	awk -v seed="$1" '
		{ line[NR] = $0 }
		/^\.LB\./ { label[++n] = substr($0, 1, length($0) - 1) }
		END {
			srand(seed)
			for (i = 1; i <= n; i++) num[i] = i
			for (i = n; i > 1; i--) { j = int(rand() * i) + 1; t = num[i]; num[i] = num[j]; num[j] = t }
			for (i = 1; i <= n; i++) to[label[i]] = ".LB" num[i]
			for (i = 1; i <= NR; i++) {
				s = line[i]; out = ""
				while (match(s, /\.LB\.[A-Za-z0-9_.]+/)) {
					out = out substr(s, 1, RSTART - 1) to[substr(s, RSTART, RLENGTH)]
					s = substr(s, RSTART + RLENGTH)
				}
				print out s
			}
		}'
}

# The real asm has labels, and each label name has the form .LB.NAME.K.
[ "$(grep -c '^\.LB' "$asm")" -gt 400 ] || fail "real: fewer than 400 labels"
if grep -E '\.LB[0-9]' "$asm" >/dev/null; then fail "real: a label of the sed step is left"; fi

# For each numbering of the labels, the awk gives the real asm back, and the object code is the
# same.
as -o "$tmp/real.o" "$asm"
for seed in 1 2 3 4 5 6 7 8; do
	gcc "$seed" < "$asm" > "$tmp/in.S"
	if cmp -s "$tmp/in.S" "$asm"; then fail "numbering $seed: the input has the new names"; fi
	awk -f "$awkf" "$tmp/in.S" > "$tmp/out.S" || fail "numbering $seed: the awk fails"
	cmp -s "$tmp/out.S" "$asm" || fail "numbering $seed: the names change"
	as -o "$tmp/in.o" "$tmp/in.S"
	cmp -s "$tmp/in.o" "$tmp/real.o" || fail "numbering $seed: the object code changes"
done

# A new function with labels, at the start, in the middle or at the end, does not change the
# names of the other functions.
extra=_ZN12_GLOBAL__N_15Extra3newEv
types=$(grep -c '^	\.type' "$asm")
for at in 1 $((types / 2)) $((types + 1)); do
	gcc "$at" < "$asm" | awk -v at="$at" -v f="$extra" '
		function add() {
			print "\t.type\t" f ", @function"; print f ":"; print "\tjne\t.LB9002"; print ".LB9001:"
			print "\tjmp\t.LB9001"; print ".LB9002:"; print "\tret"; print "\t.size\t" f ", .-" f
		}
		/^\t\.type/ && ++k == at { add() }
		{ print }
		END { if (k < at) add() }' > "$tmp/in.S"
	awk -f "$awkf" "$tmp/in.S" > "$tmp/out.S" || fail "add at $at: the awk fails"
	grep -q '^\.LB\.Extra\.new\.1:$' "$tmp/out.S" || fail "add at $at: no label .LB.Extra.new.1"
	awk -v f="$extra" '$0 == "\t.type\t" f ", @function" { skip = 1 } !skip { print } skip && /^\t\.size/ { skip = 0 }' \
		"$tmp/out.S" > "$tmp/rest.S"
	cmp -s "$tmp/rest.S" "$asm" || fail "add at $at: the names of the other functions change"
done

# expect NAME IN OUT: the awk changes IN to OUT.
expect() {
	if ! printf '%s' "$2" | awk -f "$awkf" > "$tmp/got" 2> "$tmp/err"; then
		fail "$1: the awk fails: $(cat "$tmp/err")"
	elif [ "$(cat "$tmp/got")" != "$3" ]; then
		fail "$1: got $(cat "$tmp/got")"
	else
		echo "ok $1"
	fi
}
# reject NAME IN: the awk fails on IN and prints one error.
reject() {
	if printf '%s' "$2" | awk -f "$awkf" > /dev/null 2> "$tmp/err"; then
		fail "$1: the awk accepts it"
	elif [ "$(grep -c '^labels.awk: ' "$tmp/err")" -ne 1 ] || [ "$(grep -c '' "$tmp/err")" -ne 1 ]; then
		fail "$1: not one error message: $(cat "$tmp/err")"
	else
		echo "ok $1: $(cat "$tmp/err")"
	fi
}
T=$(printf '\t')
fn() { printf '%s:\n%s\n%s.size%s%s, .-%s\n' "$1" "$2" "$T" "$T" "$1" "$1"; }

expect empty "" ""
expect "no labels" "$(fn f "${T}ret")" "$(fn f "${T}ret")"
expect "outside a function" "$T.text$T.LC0" "$T.text$T.LC0"
expect "forward reference" "$(fn f "${T}je$T.LB7
.LB7:
${T}ret")" "$(fn f "${T}je$T.LB.f.0
.LB.f.0:
${T}ret")"
expect "backward reference" "$(fn f ".LB7:
${T}jmp$T.LB7")" "$(fn f ".LB.f.0:
${T}jmp$T.LB.f.0")"
expect "order of definition" "$(fn f ".LB9:
.LB3:
.LB12:
${T}je$T.LB3")" "$(fn f ".LB.f.0:
.LB.f.1:
.LB.f.2:
${T}je$T.LB.f.1")"
expect "number prefix" "$(fn f ".LB1:
.LB12:
${T}je$T.LB12
${T}je$T.LB1")" "$(fn f ".LB.f.0:
.LB.f.1:
${T}je$T.LB.f.1
${T}je$T.LB.f.0")"
expect "two functions" "$(fn f ".LB1:")
$(fn g ".LB2:
${T}jmp$T.LB2")" "$(fn f ".LB.f.0:")
$(fn g ".LB.g.0:
${T}jmp$T.LB.g.0")"
expect "other local names" "$(fn f "${T}leaq$T.LC0(%rip), %rax
${T}jmp$T.L5
.LB1:")" "$(fn f "${T}leaq$T.LC0(%rip), %rax
${T}jmp$T.L5
.LB.f.0:")"
expect "member" "$(fn _ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE ".LB4:")" \
	"$(fn _ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE ".LB.Emission.permute.0:")"
expect "const member" "$(fn _ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot ".LB4:")" \
	"$(fn _ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot ".LB.Emission.isSpilled.0:")"
expect "free function" "$(fn _Z3foov ".LB4:")" "$(fn _Z3foov ".LB.foo.0:")"
expect "member and extern C" "$(fn _ZN12_GLOBAL__N_18Emission3popEv ".LB1:")
$(fn pop ".LB2:")" "$(fn _ZN12_GLOBAL__N_18Emission3popEv ".LB.Emission.pop.0:")
$(fn pop ".LB.pop.0:")"

reject "label of another function" "$(fn f ".LB1:")
$(fn g "${T}jmp$T.LB1")"
reject "undefined label" "$(fn f "${T}jmp$T.LB1")"
reject "label outside a function" ".LB1:"
reject "reference outside a function" "$T.quad$T.LB1"
reject "same prefix" "$(fn _ZN12_GLOBAL__N_11A1fEv "${T}ret")
$(fn _ZN12_GLOBAL__N_11A1fEi "${T}ret")"
reject "no prefix" "$(fn _ZL3barv "${T}ret")"
reject "no end" "f:
${T}ret"

[ "$fails" -eq 0 ] || { echo "labels_test: $fails checks fail"; exit 1; }
echo "labels_test: all checks pass"
