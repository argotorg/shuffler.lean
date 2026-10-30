#!/usr/bin/env bash
# Disassemble the code of build_bottom_up.S in the binary $1, from its first function
# (Emission::isSpilled, by its g++ name) to the end of its last function, the symbol
# permute_at_lowest_height. Print "start ADDR" and "stop ADDR", then "ADDR SIZE KIND TEXT"
# for each instruction: ADDR in hex, SIZE in bytes, KIND "pad" for an alignment nop and
# "instr" for all else, TEXT in AT&T syntax with a width suffix on each mnemonic
# (objdump -M suffix).
set -euo pipefail
bin=$1

# The addresses are only fixed if the binary is not position independent.
if [ "$(readelf -h "$bin" | awk '$1 == "Type:" { print $2 }')" != EXEC ]; then
	echo "bin_objdump: $bin is not linked with -no-pie; remove it and run make -C c" >&2
	exit 1
fi
sym() { nm -S "$bin" | awk -v s="$1" '$4 == s { print $1, $2 }'; }
read -r start _ < <(sym _ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot)
read -r last lsize < <(sym permute_at_lowest_height)
start=$(printf '%x' $((16#$start)))
stop=$(printf '%x' $((16#$last + 16#$lsize)))
echo "start $start"
echo "stop $stop"
objdump -d -M suffix --insn-width=16 --start-address=0x"$start" --stop-address=0x"$stop" "$bin" \
	| awk -F'\t' '/^ *[0-9a-f]+:\t/ {
		addr = $1; gsub(/[ :]/, "", addr)
		size = split($2, bytes, " ")
		# gcc and ld fill alignment gaps with these nop forms. "xchgw %ax,%ax" is the
		# 2-byte nop 66 90.
		kind = $3 ~ /^((data16|cs) )*nop[wlq]?( |$)|^xchgw +%ax,%ax$/ ? "pad" : "instr"
		print addr, size, kind, $3
	}'
