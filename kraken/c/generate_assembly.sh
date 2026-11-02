#!/usr/bin/env bash
# Generate the GCC assembly read by the proofs and linked by the test harnesses.
set -euo pipefail
compiler=$1
output=$2
version=$("$compiler" -dumpfullversion -dumpversion)
if [ "$version" != 15.3.0 ]; then
	echo "assembly generation requires GCC 15.3.0; got $version from $compiler" >&2
	exit 1
fi
mkdir -p "$(dirname "$output")"
tmp=$(mktemp -d "$(dirname "$output")/assembly.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# Disable the hardening added by the Nix GCC wrapper and omit .ident directives.
"$compiler" -std=c++23 -O1 -fno-ident -fno-asynchronous-unwind-tables -fcf-protection=none \
	-fomit-frame-pointer -fzero-call-used-regs=skip -fno-stack-protector -fno-pic \
	-fno-stack-clash-protection -ffreestanding -fno-exceptions -fno-rtti \
	-fno-threadsafe-statics -nostdlib++ -S shuffler/test_wrappers.cpp -o "$tmp/raw.S"

# Give local labels names that depend only on their function.
sed 's/^\.L\([0-9]\)/.LB\1/; s/\(	j[a-z]*	\)\.L\([0-9]\)/\1.LB\2/' "$tmp/raw.S" \
	| awk -f labels.awk > "$tmp/program.S"
mv "$tmp/program.S" "$output"
