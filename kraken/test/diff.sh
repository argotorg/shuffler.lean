#!/usr/bin/env bash
# Run the compiled permute.S, the Lean model and the original Shuffler.Permute.permute
# on the same permutations, and compare the results.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

make -C "$root/kraken/c" -s
(cd "$root/kraken" && lake build model >/dev/null)
(cd "$root" && lake build Shuffler.Permute.Defs >/dev/null)

"$root/kraken/c/harness" gen > "$tmp/perms"
"$root/kraken/c/harness" run < "$tmp/perms" > "$tmp/c"
"$root/kraken/.lake/build/bin/model" < "$tmp/perms" > "$tmp/model"
(cd "$root" && lake env lean --run kraken/test/OriginalMain.lean) < "$tmp/perms" > "$tmp/orig"

cmp "$tmp/c" "$tmp/model"
cmp "$tmp/c" "$tmp/orig"
echo "C, model and original agree on $(wc -l < "$tmp/perms") permutations"
