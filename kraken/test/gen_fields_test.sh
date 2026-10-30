#!/usr/bin/env bash
# Tests of test/gen_fields.sh.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
gen=$dir/test/gen_fields.sh
out=$dir/BbuKraken/Sep/Fields.lean
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# The real layout: the checked-in file is current.
"$gen" --check > /dev/null
grep -q '^def SIZE : Nat := 16472$' "$out"
echo "ok: real layout"

# A copy of the sources, with one change. The generator must fail and must not write the file.
fails() { # expected-message sed-script
	rm -rf "$tmp/c"; mkdir "$tmp/c"
	cp "$dir/c/build_bottom_up.cpp" "$tmp/c/"
	sed -i "$2" "$tmp/c/build_bottom_up.cpp"
	cmp -s "$dir/c/build_bottom_up.cpp" "$tmp/c/build_bottom_up.cpp" && { echo "FAIL: no change: $2"; exit 1; }
	local before; before=$(sha1sum "$out")
	if BBU_SRC=$tmp/c "$gen" 2> "$tmp/err" > /dev/null; then
		echo "FAIL: the generator did not fail: $2"; exit 1
	fi
	grep -qF "$1" "$tmp/err" || { echo "FAIL: message"; cat "$tmp/err"; exit 1; }
	[ "$(sha1sum "$out")" = "$before" ] || { echo "FAIL: $out changed"; exit 1; }
}

# A member that is not in the probe makes a hole.
fails 'm_stack.m_data: offset 32, not 24' 's|^\tstd::uint8_t const\* m_spills;$|&\n\tstd::uint32_t m_pad;|'
echo "ok: a hole fails"

# A member after the last member of the probe.
fails 'the members end at 16472, sizeof is 16480' 's|^\tMapping const& m_plannedMapping;$|&\n\tstd::uint8_t m_pad;|'
echo "ok: a member at the end fails"

# A member in the place of the reference: R accepts only a reference member.
fails 'static assertion failed' 's|^\tMapping const& m_plannedMapping;$|\tMapping const* m_plannedMapping;|'
echo "ok: R of a member that is not a reference fails"

# Elements of 4 bytes: a `StackOffset` of 4 bytes.
fails 'm_mapping.m_destinationOf: element size 4, not 8' \
	'/^struct StackOffset$/,/^};$/s|^\tstd::size_t value;$|\tstd::uint32_t value;|'
echo "ok: an element of 4 bytes fails"

# A different array size: no hole, but --check finds that the file is not current.
rm -rf "$tmp/c"; mkdir "$tmp/c"
cp "$dir/c/build_bottom_up.cpp" "$tmp/c/"
sed -i 's|maxStackSize = 1024|maxStackSize = 512|' "$tmp/c/build_bottom_up.cpp"
grep -q 'maxStackSize = 512' "$tmp/c/build_bottom_up.cpp"
if BBU_SRC=$tmp/c "$gen" --check 2> "$tmp/err" > /dev/null; then
	echo "FAIL: --check did not find the change"; exit 1
fi
grep -q 'is not current' "$tmp/err"
echo "ok: --check finds a stale file"
