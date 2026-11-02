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
# NAME... of the Lean file FILE (with an optional module header).
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$dir/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

if [ $# -eq 0 ]; then
	(cd "$root" && nice lake build -q Theorems FlatShuffler.Bin FlatShuffler.Unit.Plan.PlannerRunBin >/dev/null)
	printf 'module\nimport Theorems.Main\nimport all FlatShuffler.PlanFinal\nimport all FlatShuffler.Bin\nimport FlatShuffler.Unit.Plan.PlannerRunBin\n' > "$tmp/final.lean"
	set -- "$tmp/final.lean" FlatShuffler.buildBottomUp_correct FlatShuffler.buildBottomUp_binary_correct \
		FlatShuffler.planner_helpers_correct FlatShuffler.emission_run_correct FlatShuffler.planner_classify_correct \
		FlatShuffler.planner_resolve_correct FlatShuffler.planner_run_correct FlatShuffler.planner_run_binary_correct \
		FlatShuffler.plan_correct FlatShuffler.plan_binary_correct \
		ShufflerVerification.planner_assembly_satisfies_model_contract ShufflerVerification.planner_binary_satisfies_model_contract ShufflerVerification.planner_flat_execution_matches_model \
		ShufflerVerification.planner_assembly_matches_model ShufflerVerification.planner_binary_matches_model \
		ShufflerVerification.planner_flat_execution_does_not_assert \
		ShufflerVerification.planner_assembly_satisfies_normal_return_contract ShufflerVerification.planner_binary_satisfies_normal_return_contract \
		ShufflerVerification.planner_assembly_returns_normally ShufflerVerification.planner_binary_returns_normally \
		ShufflerVerification.PlannerInputsValidForNormalReturn.inputAssumptions \
		ShufflerVerification.planner_flat_execution_transfers_model_postcondition \
		ShufflerVerification.planner_assembly_transfers_model_postcondition ShufflerVerification.planner_binary_transfers_model_postcondition \
		ShufflerVerification.planner_model_establishes_correctness ShufflerVerification.planner_model_returns_correct_plan_or_blocked \
		ShufflerVerification.planner_assembly_returns_correct_plan_or_blocked ShufflerVerification.planner_binary_returns_correct_plan_or_blocked
fi
src=$(realpath "$1")
shift
names=$(printf '"%s", ' "$@")

# A user `axiom` with the name and the type of a bv_decide axiom passes the check
# below: Lean adds the bv_decide axiom as a plain axiom declaration with no mark. Thus
# no `axiom` declaration is allowed in FILE or in the Lean files of this repository. The
# check below still runs: it is the only check for the imported packages.
decls=$(git -C "$root" ls-files --cached --others --exclude-standard -z '*.lean' |
	(cd "$root" && while IFS= read -r -d '' file; do
		if [ -f "$file" ]; then printf '%s\0' "$file"; fi
	done | xargs -0 awk -f "$dir/test/axiom_decls.awk" "$src"))
ok=true
if [ -n "$decls" ]; then
	printf 'axioms: axiom declaration not allowed:\n%s\n' "$decls" >&2
	ok=false
fi

{
	echo 'module'
	echo 'import Lean'
	# Retain module visibility. Legacy definitions and imports are public.
	awk 'NR == FNR {
	    if ($0 ~ /^module([[:space:]]|$)/) modern = 1
	    if ($0 ~ /^(public )?(meta )?import /) last = FNR
	    next
	  }
	  FNR == 1 && !modern && !last { print "@[expose] public section" }
	  /^module([[:space:]]|$)/ { next }
	  !modern && /^import / {
	    if ($2 == "all") {
	      print "public import " $3
	      print
	    } else if ($2 == "meta") {
	      print "public " $0
	    } else {
	      print "public " $0
	      print "import all " $2
	    }
	    if (FNR == last) print "\n@[expose] public section\n"
	    next
	  }
	  { print }
	  FNR == last && !modern { print "\n@[expose] public section\n" }' "$src" "$src"
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

if ! (cd "$root" && nice lake env lean -DElab.async=false "$tmp/Check.lean") > "$tmp/out" 2>&1; then
	grep -v 'declaration uses `sorry`' "$tmp/out" >&2
	exit 1
fi
cat "$tmp/out"
$ok
