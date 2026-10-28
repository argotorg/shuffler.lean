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
expect_fail immediate dis '0,/\$0x1,%rsi/s//$0x2,%rsi/'
expect_fail negative dis '0,/\$0xffffffffffffffff/s//$0xfffffffffffffffe/'
expect_fail register dis '0,/%rdx,%rsi/s//%rdx,%rdi/'
expect_fail displacement dis '0,/0x840(/s//0x848(/'
expect_fail mnemonic dis '0,/movl /s//movw /'
expect_fail target dis '0,/jbe    4021e6/s//jbe    4021e5/'
expect_fail call dis '0,/4021e7 <position_of>/s//4021e6 <position_of>/'
expect_fail movzx dis '0,/movzbl %al,%eax/s//movzwl %ax,%eax/'
expect_fail cmov dis '0,/cmovneq/s//cmoveq/'
expect_fail kind dis '0,/ pad /s// instr /'
expect_fail no-pad dis '0,/ pad /{/ pad /d}'
expect_fail last dis '$d'
expect_fail extra dis '$a 402b2b 1 instr ret'
expect_fail start dis 's/^start .*/start 4021c1/'
expect_fail stop dis 's/^stop .*/stop 402b2c/'
expect_fail size host '2s/^\([0-9a-f]*\) 5 /\1 6 /'
expect_fail address host '2s/^4021c0 /4021c1 /'
expect_fail label host 's/^4021e6 0 \.LB1:/4021e5 0 .LB1:/'
expect_fail text host '0,/cmpq \$1, %rsi/s//cmpq $1, %rdi/'
expect_fail width host '0,/movq \$-1, %rax/s//movl $-1, %eax/'
expect_fail unknown-label host '0,/jbe \.LB1/s//jbe .LBX/'

if [ "$fails" -ne 0 ]; then exit 1; fi
echo "bin_check_test: all changes are rejected"
