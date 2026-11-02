#!/usr/bin/env bash
# Run the compiled build_bottom_up.S (through build/kraken/c/bbu_harness), the PR31 model
# Shuffler.Emission.buildBottomUp (bbu_pr31 of the root project) and the flat model
# Bbu.Flat.build_bottom_up (bbu_flat) on the same states, and compare the full results:
# the status, the blocked offset and excess, the operations and the final stack. The two
# models also print the destination of each slot of the final stack; the C interface
# does not give it, so the C++ is compared without it. Run it with nice: it takes some
# minutes.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cmake -S "$root" -B "$root/build" -G Ninja -DBUILD_TESTING=ON >/dev/null
cmake --build "$root/build" --target shuffler_bbu_harness >/dev/null
(cd "$root" && lake build bbu_pr31 >/dev/null)
(cd "$root" && lake build ShufflerKraken/bbu_flat >/dev/null)

"$root/build/kraken/c/bbu_harness" gen > "$tmp/states"
"$root/build/kraken/c/bbu_harness" run < "$tmp/states" > "$tmp/c"
"$root/.lake/build/bin/bbu_pr31" < "$tmp/states" > "$tmp/pr31"
"$root/kraken/.lake/build/bin/bbu_flat" < "$tmp/states" > "$tmp/flat"

# A line of bbu_pr31 without its last field (the destinations).
sed 's/ |[^|]*$//' "$tmp/pr31" > "$tmp/pr31-c"

for impl in c pr31 flat; do
	if grep -n -m 5 -e '^invalid' -e '^error' -e '^bad input' "$tmp/$impl"; then
		echo "$impl: lines that must not occur" >&2
		exit 1
	fi
done
# impl, the file of impl, the file of the model
for check in "c c pr31-c" "flat flat pr31"; do
	set -- $check
	if ! cmp "$tmp/$2" "$tmp/$3"; then
		paste -d '\n' "$tmp/states" "$tmp/$3" "$tmp/$2" /dev/null \
			| awk -v impl="$1" 'NR % 4 == 2 { o = $0 } NR % 4 == 3 && $0 != o { print s; print "pr31 " o; print impl " " $0; if (++k == 3) exit } NR % 4 == 1 { s = $0 }'
		exit 1
	fi
done
echo "C++, PR31 model and flat model agree on $(wc -l < "$tmp/states") states ($(grep -c '^ok' "$tmp/c") ok, $(grep -c '^blocked' "$tmp/c") blocked, $(grep -c '^assertion' "$tmp/c") assertion)"
