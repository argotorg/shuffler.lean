#!/usr/bin/env bash
# Run the compiled build_bottom_up.S, the model Bbu.buildBottomUp and the original
# Shuffler.Emission.buildBottomUp on the same valid states, and compare the results.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

make -C "$root/kraken/c" -s
(cd "$root" && lake build Shuffler.BuildBottomUp.Defs >/dev/null)
(cd "$root/kraken" && lake build bbu_model >/dev/null)

"$root/kraken/c/bbu_harness" gen > "$tmp/states"
"$root/kraken/c/bbu_harness" run < "$tmp/states" > "$tmp/c"
"$root/kraken/.lake/build/bin/bbu_model" < "$tmp/states" > "$tmp/model"
(cd "$root" && lake env lean --run kraken/test/BuildBottomUpMain.lean) < "$tmp/states" > "$tmp/orig"

if grep -n -m 5 -e '^assertion' -e '^invalid' "$tmp/orig"; then
	echo "the original fails on generated states" >&2
	exit 1
fi
for impl in c model; do
	if ! cmp "$tmp/$impl" "$tmp/orig"; then
		paste -d '\n' "$tmp/states" "$tmp/orig" "$tmp/$impl" /dev/null \
			| awk -v impl="$impl" 'NR % 4 == 2 { o = $0 } NR % 4 == 3 && $0 != o { print s; print "orig  " o; print impl " " $0; if (++k == 3) exit } NR % 4 == 1 { s = $0 }'
		exit 1
	fi
done
echo "C, model and original agree on $(wc -l < "$tmp/states") states ($(grep -c '^ok' "$tmp/c") ok, $(grep -c '^blocked' "$tmp/c") blocked)"
