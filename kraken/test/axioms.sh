#!/usr/bin/env bash
# Fail if a final theorem depends on an axiom that is not allowed. Allowed:
#   propext, Classical.choice, Quot.sound   the axioms of Lean core
#   D._native.bv_decide.ax_I                bv_decide (one axiom for each use), if its
#                                           type is
#                                           `Std.Tactic.BVDecide.Reflect.verifyBVExpr _ _ = true`
# sorryAx is not allowed, and the axiom D._native.native_decide.ax_I of native_decide is
# not allowed. An `axiom` declaration in FILE or in a Lean file of this package is not
# allowed (test/axiom_decls.awk finds them).
#
# Usage: axioms.sh [FILE NAME...]
# With no arguments, check the final theorems. With arguments, check the theorems
# NAME... of the Lean file FILE (FILE starts with its imports).
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

if [ $# -eq 0 ]; then
	(cd "$dir" && lake build -q BbuKraken.Bin >/dev/null)
	printf 'import BbuKraken.Bin\n' > "$tmp/final.lean"
	set -- "$tmp/final.lean" Bbu.buildBottomUp_correct Bbu.bbu_harness_correct
fi
src=$1
shift
names=$(printf '"%s", ' "$@")

# A user `axiom` with the name and the type of a bv_decide axiom passes the check
# below: Lean adds the bv_decide axiom as a plain axiom declaration with no mark. Thus
# no `axiom` declaration is allowed in FILE or in the Lean files of this package. The
# check below still runs: it is the only check for the imported packages.
decls=$(find "$dir" -name .lake -prune -o -name '*.lean' -print0 |
	xargs -0 awk -f "$dir/test/axiom_decls.awk" "$src")
ok=true
if [ -n "$decls" ]; then
	printf 'axioms: axiom declaration not allowed:\n%s\n' "$decls" >&2
	ok=false
fi

{
	echo 'import Lean'
	cat "$src"
	cat <<EOF

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let core := [\`propext, \`Classical.choice, \`Quot.sound]
  let bvDecide : Name → Bool
    | n@(.str (.str (.str _ "_native") "bv_decide") s) => s.startsWith "ax_" &&
      match env.find? n with
      | some (.axiomInfo a) => a.type.isAppOfArity \`Eq 3 &&
          a.type.appFn!.appArg!.isAppOfArity \`Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 &&
          a.type.appArg! == mkConst \`Bool.true
      | _ => false
    | _ => false
  let mut bad := #[]
  for s in [${names%, }] do
    let n := s.toName
    unless env.contains n do throwError "axioms: unknown theorem {n}"
    let axs ← collectAxioms n
    logInfo m!"{n}: {axs}"
    for a in axs do
      unless core.contains a || bvDecide a do bad := bad.push (n, a)
  unless bad.isEmpty do throwError "axioms: not allowed: {bad}"
EOF
} > "$tmp/Check.lean"

if ! (cd "$dir" && lake env lean "$tmp/Check.lean") > "$tmp/out" 2>&1; then
	grep -v 'declaration uses `sorry`' "$tmp/out" >&2
	exit 1
fi
cat "$tmp/out"
$ok
