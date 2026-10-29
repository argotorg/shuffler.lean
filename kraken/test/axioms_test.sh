#!/usr/bin/env bash
# Test axioms.sh: it must accept State.permute_spec and a bv_decide proof, and reject
# sorry, native_decide, a user axiom, a forged bv_decide axiom and an unknown name.
# With no arguments it must report the 3 final theorems. While a unit proof has a sorry,
# that mode fails; then sorryAx must be the only axiom that it rejects.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fails=0
# check NAME ok|fail BODY THEOREM: axioms.sh on the Lean text BODY (after the imports)
# and THEOREM must pass (ok) or fail (fail).
check() {
	{
		printf 'import BbuKraken.Bin\nimport PermuteKraken.Proof\nimport Std.Tactic.BVDecide\n'
		printf '%s\n' "$3"
	} > "$tmp/$1.lean"
	if "$here/axioms.sh" "$tmp/$1.lean" "$4" > "$tmp/out" 2>&1; then got=ok; else got=fail; fi
	if [ "$got" = "$2" ]; then
		echo "ok $1: $(grep -m1 -e 'not allowed' -e 'unknown' -e "^$4:" "$tmp/out")"
	else
		echo "FAIL $1: expected $2, got $got"; cat "$tmp/out"; fails=$((fails + 1))
	fi
}

"$here/axioms.sh" > "$tmp/final" 2>&1 || true
n=$(grep -c -e '^Bbu.buildBottomUp_correct:' -e '^Bbu.bbu_harness_correct:' \
	-e '^State.permute_spec:' "$tmp/final" || true)
other=$(grep -o 'not allowed: .*' "$tmp/final" | grep -o '([^()]*)' | grep -v ', sorryAx)$' || true)
if [ "$n" -eq 3 ] && [ -z "$other" ]; then
	echo "ok final: $n theorems; $(grep -o 'sorryAx)' "$tmp/final" | wc -l) use sorryAx"
else
	echo "FAIL final"; cat "$tmp/final"; fails=$((fails + 1))
fi
check permute ok '' State.permute_spec

# A copy of State.L3_eP with each closing step.
eP() {
	printf 'theorem State.%s (p a : BitVec 64) :\n' "$1"
	printf '    p + a * 2#64 + BitVec.ofInt 64 (Int64.toInt 0) = p + .ofNat 64 (2 * a.toNat) := by\n'
	printf '  %s\n' "$2"
}

check copy ok "$(eP eP_copy 'simp; bv_omega')" State.eP_copy
check bv_decide ok '
theorem Bbu.mul_lt (x y : BitVec 16) (hx : x < 100#16) (hy : y < 100#16) :
    x * y < 10000#16 := by bv_decide' Bbu.mul_lt
if ! grep -q '_native.bv_decide.ax_' "$tmp/out"; then
	echo "FAIL bv_decide: the proof adds no bv_decide axiom"; fails=$((fails + 1))
fi
check sorry fail "$(eP eP_sorry 'simp; sorry')" State.eP_sorry
check sorry-final fail '
open Std.WP Lean.Order
open scoped Program.WP
theorem Bbu.bbu_harness_sorry :
    letI := Bbu.binLinked.decls
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ Bbu.TopPre s ⦄ Bbu.buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ Bbu.TopPost s t ∧ (Bbu.topMod s).Agree s t ⦄ :=
  sorry' Bbu.bbu_harness_sorry
check sorry-used fail "$(eP eP_sorry 'simp; sorry')
theorem State.eP_use (p a : BitVec 64) :
    p + a * 2#64 + BitVec.ofInt 64 (Int64.toInt 0) = p + .ofNat 64 (2 * a.toNat) :=
  State.eP_sorry p a" State.eP_use
check native_decide fail '
theorem Bbu.sizesOk_nd : Bbu.sizesOk [.label "a"] [1] = false := by native_decide' Bbu.sizesOk_nd
check user-axiom fail '
axiom Bbu.ax : False
theorem Bbu.uses_ax : 1 = 2 := Bbu.ax.elim' Bbu.uses_ax
check forged-bv fail '
axiom Bbu.f._native.bv_decide.ax_1_1 : False
theorem Bbu.f : 1 = 2 := Bbu.f._native.bv_decide.ax_1_1.elim' Bbu.f
check unknown fail '' Bbu.no_such_theorem

if [ "$fails" -ne 0 ]; then exit 1; fi
