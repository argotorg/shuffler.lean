#!/usr/bin/env bash
# Test test/bin_check.awk: it must accept the real listings and reject each change.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
"$dir/test/bin_check.sh" "$tmp" >/dev/null

fails=0
# expect_fail NAME FILE SED: change FILE (host or dis) with SED; the check must fail.
expect_fail() {
	cp "$tmp/host" "$tmp/h"; cp "$tmp/dis" "$tmp/d"
	sed -i "$3" "$tmp/${2:0:1}"
	if cmp -s "$tmp/h" "$tmp/host" && cmp -s "$tmp/d" "$tmp/dis"; then
		echo "FAIL $1: the change does nothing"; fails=$((fails + 1))
	elif awk -f "$dir/test/bin_check.awk" "$tmp/h" "$tmp/d" 2>"$tmp/err" >/dev/null; then
		echo "FAIL $1: the check accepts it"; fails=$((fails + 1))
	else
		echo "ok $1: $(cat "$tmp/err")"
	fi
}

awk -f "$dir/test/bin_check.awk" "$tmp/host" "$tmp/dis" >/dev/null

# The addresses and the displacement come from the listings: the layout of the
# binary changes with the code.
hex() { printf '%x' $((0x$1 + $2)); }
read -r first size _ < <(sed -n 2p "$tmp/host")
lb1=$(awk '$3 == ".LB.Emission.isSpilled.0:" { print $1; exit }' "$tmp/host")
jbe=$(grep -m1 -o 'jbe  *[0-9a-f]*' "$tmp/dis" | awk '{ print $2 }')
push=_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset
call=$(grep -m1 -o "[0-9a-f]* <$push>" "$tmp/dis" | cut -d' ' -f1)
disp=$(grep -m1 -o '0x[0-9a-f]*(' "$tmp/dis" | sed 's/^0x//; s/($//')
start=$(awk '$1 == "start" { print $2 }' "$tmp/dis")
stop=$(awk '$1 == "stop" { print $2 }' "$tmp/dis")

expect_fail immediate dis '0,/\$0x1,%rax/s//$0x2,%rax/'
expect_fail negative dis '0,/\$0xffffffffffffffff/s//$0xfffffffffffffffe/'
expect_fail register dis '0,/%rdx,%rsi/s//%rdx,%rdi/'
expect_fail displacement dis "0,/0x$disp(/s//0x$(hex "$disp" 8)(/"
expect_fail mnemonic dis '0,/movl /s//movw /'
expect_fail target dis "0,/jbe  *$jbe/s//jbe    $(hex "$jbe" -1)/"
expect_fail call dis "0,/$call <$push>/s//$(hex "$call" -1) <$push>/"
expect_fail movzx dis '0,/movzbl %dl,%eax/s//movzwl %dx,%eax/'
expect_fail cmov dis '0,/cmoveq/s//cmovneq/'
expect_fail and-l dis '0,/andl *%r10d,%esi/s//andq   %r10,%rsi/'
expect_fail or-b dis '0,/orb *%dl,%al/s//orw    %dx,%ax/'
expect_fail movabs dis '0,/movabsq *\(\$0x[0-9a-f]*\),%rbp/s//movabsq \1,%rbx/'
expect_fail kind dis '0,/ pad /s// instr /'
expect_fail no-pad dis '0,/ pad /{/ pad /d}'
expect_fail last dis '$d'
expect_fail extra dis "\$a $stop 1 instr ret"
expect_fail start dis "s/^start .*/start $(hex "$start" 1)/"
expect_fail stop dis "s/^stop .*/stop $(hex "$stop" 1)/"
expect_fail size host "2s/^\([0-9a-f]*\) $size /\1 $((size + 1)) /"
expect_fail address host "2s/^$first /$(hex "$first" 1) /"
expect_fail label host "s/^$lb1 0 \\.LB\\.Emission\\.isSpilled\\.0:/$(hex "$lb1" -1) 0 .LB.Emission.isSpilled.0:/"
expect_fail text host '0,/cmpb \$1, %dl/s//cmpb $1, %bl/'
expect_fail width host '0,/movq \$-1, %rax/s//movl $-1, %eax/'
expect_fail unknown-label host '0,/jbe \.LB[A-Za-z0-9_.]*/s//jbe .LBX/'

if [ "$fails" -ne 0 ]; then exit 1; fi
echo "bin_check_test: all changes are rejected"
