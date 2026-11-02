#!/usr/bin/env bash
# Test axioms.sh: it must accept FlatShuffler.buildBottomUp_correct and a bv_decide proof, and reject
# sorry, native_decide, a user axiom, a forged bv_decide axiom and an unknown name.
# With no arguments it must accept and report all 28 listed theorems.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fails=0
# check NAME ok|fail BODY THEOREM: axioms.sh on the Lean text BODY (after the imports)
# and THEOREM must pass (ok) or fail (fail).
check() {
	{
		printf 'import FlatShuffler.Bin\nimport Std.Tactic.BVDecide\n'
		printf '%s\n' "$3"
	} > "$tmp/$1.lean"
	if "$here/axioms.sh" "$tmp/$1.lean" "$4" > "$tmp/out" 2>&1; then got=ok; else got=fail; fi
	if [ "$2" = fail ] && [ "$1" != unknown ] && ! grep -q "^$4:" "$tmp/out"; then
		echo "FAIL $1: the theorem was not checked"; cat "$tmp/out"; fails=$((fails + 1))
		return
	fi
	local reason=''
	case "$1" in
		sorry*) reason=sorryAx ;;
		native_decide) reason=_native.native_decide.ax_ ;;
	esac
	if [ -n "$reason" ] && ! grep -qF "$reason" "$tmp/out"; then
		echo "FAIL $1: no $reason axiom"; cat "$tmp/out"; fails=$((fails + 1))
		return
	fi
	if [ "$got" = "$2" ]; then
		echo "ok $1: $(grep -m1 -e 'not allowed' -e 'unknown' -e "^$4:" "$tmp/out")"
	else
		echo "FAIL $1: expected $2, got $got"; cat "$tmp/out"; fails=$((fails + 1))
	fi
}

# axiom_decls.awk must find the lines marked `-- yes` and no other line.
cat > "$tmp/decls.lean" <<'EOF'
axiom a : False -- yes
  axiom b : False -- yes
private axiom c : False -- yes
@[simp] noncomputable axiom d : False -- yes
/-- doc -/ axiom e : False -- yes
/- a /- nested -/ comment -/ axiom f : False -- yes
axiomatic : Nat
theorem axiom_g : True := trivial
-- axiom h : False
/-
axiom i : False
/- -/
axiom j : False
-/
def s := "/-"
axiom k : False -- yes
def t := "\"/-"
axiom l : False -- yes
EOF
want=$(grep -n -- '-- yes$' "$tmp/decls.lean" | cut -d: -f1)
got=$(awk -f "$here/axiom_decls.awk" "$tmp/decls.lean" | cut -d: -f2)
if [ "$got" = "$want" ]; then
	echo "ok axiom_decls: lines $(echo $got)"
else
	echo "FAIL axiom_decls: expected lines $(echo $want), got $(echo $got)"; fails=$((fails + 1))
fi

if "$here/axioms.sh" > "$tmp/final" 2>&1; then final_ok=true; else final_ok=false; fi
n=$(grep -c -e '^FlatShuffler.buildBottomUp_correct:' -e '^FlatShuffler.buildBottomUp_binary_correct:' \
	-e '^FlatShuffler.planner_helpers_correct:' -e '^FlatShuffler.emission_run_correct:' \
	-e '^FlatShuffler.planner_classify_correct:' -e '^FlatShuffler.planner_resolve_correct:' \
	-e '^FlatShuffler.planner_run_correct:' -e '^FlatShuffler.planner_run_binary_correct:' \
	-e '^FlatShuffler.plan_correct:' -e '^FlatShuffler.plan_binary_correct:' \
	-e '^ShufflerVerification.planner_assembly_satisfies_model_contract:' -e '^ShufflerVerification.planner_binary_satisfies_model_contract:' \
	-e '^ShufflerVerification.planner_flat_execution_matches_model:' -e '^ShufflerVerification.planner_assembly_matches_model:' \
	-e '^ShufflerVerification.planner_binary_matches_model:' \
	-e '^ShufflerVerification.planner_flat_execution_does_not_assert:' \
	-e '^ShufflerVerification.planner_assembly_satisfies_normal_return_contract:' \
	-e '^ShufflerVerification.planner_binary_satisfies_normal_return_contract:' \
	-e '^ShufflerVerification.planner_assembly_returns_normally:' \
	-e '^ShufflerVerification.planner_binary_returns_normally:' \
	-e '^ShufflerVerification.PlannerInputsValidForNormalReturn.inputAssumptions:' \
	-e '^ShufflerVerification.planner_flat_execution_transfers_model_postcondition:' \
	-e '^ShufflerVerification.planner_assembly_transfers_model_postcondition:' \
	-e '^ShufflerVerification.planner_binary_transfers_model_postcondition:' \
	-e '^Shuffler.Planner.run_correct:' \
	-e '^ShufflerVerification.planner_model_returns_correct_plan_or_blocked:' \
	-e '^ShufflerVerification.planner_assembly_returns_correct_plan_or_blocked:' \
	-e '^ShufflerVerification.planner_binary_returns_correct_plan_or_blocked:' "$tmp/final" || true)
other=$(grep -o 'not allowed: .*' "$tmp/final" | grep -o '([^()]*)' | grep -v ', sorryAx)$' || true)
if $final_ok && [ "$n" -eq 28 ] && [ -z "$other" ] && ! grep -q sorryAx "$tmp/final"; then
	echo "ok final: $n theorems"
else
	echo "FAIL final"; cat "$tmp/final"; fails=$((fails + 1))
fi
check buildBottomUp ok '' FlatShuffler.buildBottomUp_correct

# A bit-vector identity with each closing step.
eP() {
	printf 'theorem AuditTest.%s (p a : BitVec 64) :\n' "$1"
	printf '    p + a * 2#64 + BitVec.ofInt 64 (Int64.toInt 0) = p + .ofNat 64 (2 * a.toNat) := by\n'
	printf '  %s\n' "$2"
}

check copy ok "$(eP eP_copy 'simp; bv_omega')" AuditTest.eP_copy
check bv_decide ok '
theorem FlatShuffler.mul_lt (x y : BitVec 16) (hx : x < 100#16) (hy : y < 100#16) :
    x * y < 10000#16 := by bv_decide' FlatShuffler.mul_lt
if ! grep -q '_native.bv_decide.ax_' "$tmp/out"; then
	echo "FAIL bv_decide: the proof adds no bv_decide axiom"; fails=$((fails + 1))
fi
check sorry fail "$(eP eP_sorry 'simp; sorry')" AuditTest.eP_sorry
check sorry-final fail '
open Std.WP Lean.Order
open scoped Program.WP
theorem FlatShuffler.bbu_harness_sorry :
    letI := FlatShuffler.binLinked.decls
    FlatShuffler.Unit.UnitThmWithExit FlatShuffler.loopAsm FlatShuffler.Unit.loopA 2068 FlatShuffler.Unit.loopQ FlatShuffler.Unit.loopX :=
  sorry' FlatShuffler.bbu_harness_sorry
check sorry-used fail "$(eP eP_sorry 'simp; sorry')
theorem AuditTest.eP_use (p a : BitVec 64) :
    p + a * 2#64 + BitVec.ofInt 64 (Int64.toInt 0) = p + .ofNat 64 (2 * a.toNat) :=
  AuditTest.eP_sorry p a" AuditTest.eP_use
check native_decide fail '
theorem FlatShuffler.sizesOk_nd : FlatShuffler.sizesOk [.label "a"] [1] = false := by native_decide' FlatShuffler.sizesOk_nd
check user-axiom fail '
axiom FlatShuffler.ax : False
theorem FlatShuffler.uses_ax : 1 = 2 := FlatShuffler.ax.elim' FlatShuffler.uses_ax
check forged-bv fail '
axiom FlatShuffler.f._native.bv_decide.ax_1_1 : False
theorem FlatShuffler.f : 1 = 2 := FlatShuffler.f._native.bv_decide.ax_1_1.elim' FlatShuffler.f
if ! grep -q 'not allowed: \[(FlatShuffler.f, FlatShuffler.f._native.bv_decide.ax_1_1)\]' "$tmp/out"; then
	echo "FAIL forged-bv: the type check does not reject the axiom"; fails=$((fails + 1))
fi
check forged-bv-type fail '
axiom FlatShuffler.g._native.bv_decide.ax_1_1 :
  Std.Tactic.BVDecide.Reflect.verifyBVExpr (.const false) "" = true
theorem FlatShuffler.g : True := (fun _ => trivial) FlatShuffler.g._native.bv_decide.ax_1_1' FlatShuffler.g
# The type check accepts this axiom; only the scan for `axiom` declarations rejects it.
if grep -q 'not allowed: \[' "$tmp/out" || ! grep -q '^FlatShuffler.g: ' "$tmp/out"; then
	echo "FAIL forged-bv-type: expected the type check to accept the axiom"; fails=$((fails + 1))
fi
check unknown fail '' FlatShuffler.no_such_theorem

if [ "$fails" -ne 0 ]; then exit 1; fi
