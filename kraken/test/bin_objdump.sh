#!/usr/bin/env bash
# Disassemble the code of build_bottom_up.S and permute.S in the binary $1, from the
# symbol is_spilled to the end of the symbol permute. Print "start ADDR" and
# "stop ADDR", then "ADDR SIZE KIND TEXT" for each instruction: ADDR in hex, SIZE in
# bytes, KIND "pad" for an alignment nop and "instr" for all else, TEXT in AT&T
# syntax with a width suffix on each mnemonic (objdump -M suffix).
set -euo pipefail
bin=$1

# The addresses are only fixed if the binary is not position independent.
if [ "$(readelf -h "$bin" | awk '$1 == "Type:" { print $2 }')" != EXEC ]; then
	echo "bin_objdump: $bin is not linked with -no-pie; remove it and run make -C c" >&2
	exit 1
fi
sym() { nm -S "$bin" | awk -v s="$1" '$4 == s { print $1, $2 }'; }
read -r start _ < <(sym is_spilled)
read -r perm psize < <(sym permute)
start=$(printf '%x' $((16#$start)))
stop=$(printf '%x' $((16#$perm + 16#$psize)))
echo "start $start"
echo "stop $stop"
objdump -d -M suffix --insn-width=16 --start-address=0x"$start" --stop-address=0x"$stop" "$bin" \
	| awk -F'\t' '/^ *[0-9a-f]+:\t/ {
		addr = $1; gsub(/[ :]/, "", addr)
		size = split($2, bytes, " ")
		# gcc and ld fill alignment gaps with these nop forms.
		kind = $3 ~ /^((data16|cs) )*nop[wlq]?( |$)/ ? "pad" : "instr"
		print addr, size, kind, $3
	}'
