import LeanTools.Axioms
import Test.AxiomsLemma

/-! Tests of `LeanTools.checkAxioms` (`#gate_axioms`).

The words `native_decide`, `axiom` and `sorry` occur here on purpose: each such test shows a
refusal. -/

open Lean Std.Tactic.BVDecide Std.Tactic.BVDecide.Reflect

namespace Test.Axioms

/-! ## Accepted -/

theorem std_only (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- info: Test.Axioms.std_only: accepted, axioms [] -/
#guard_msgs in #gate_axioms std_only

theorem sat (x y : BitVec 8) : x * y = y * x := by bv_decide

/-- info: Test.Axioms.sat: accepted, axioms [propext, Classical.choice, Quot.sound, Test.Axioms.sat._native.bv_decide.ax_1_5] -/
#guard_msgs in #gate_axioms sat

/-- Offset equalities of the project: `bv_decide` closes them in preprocessing, with no new axiom. -/
theorem offset (x : BitVec 64) : x - 24 + 8 = x - 16 := by bv_decide

/-- info: Test.Axioms.offset: accepted, axioms [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #gate_axioms offset

theorem sat_1 (x y : BitVec 8) : y * x = x * y := (sat x y).symm
theorem sat_2 (x y : BitVec 8) : y * x = x * y ∧ True := ⟨sat_1 x y, trivial⟩
theorem sat_3 (x y : BitVec 8) : (y * x = x * y ∧ True) ∧ True := ⟨sat_2 x y, trivial⟩

/-- info: Test.Axioms.sat_3: accepted, axioms [propext, Classical.choice, Quot.sound, Test.Axioms.sat._native.bv_decide.ax_1_5] -/
#guard_msgs in #gate_axioms sat_3

/-- Three levels down, across a module boundary. -/
theorem imported_3 (x y : BitVec 8) : (y * x = x * y) ∧ True := ⟨(mul_comm8 x y).symm, trivial⟩

/-- info: Test.Axioms.imported_3: accepted, axioms [propext, Classical.choice, Quot.sound, _private.Test.AxiomsLemma.0.Test.Axioms.mul_comm8._native.bv_decide.ax_1_5] -/
#guard_msgs in #gate_axioms imported_3

/-- A copy of a true `bv_decide` claim, written by hand with the names of `bv_decide`. The gate
accepts it: the claim is true, and the gate does not ask who wrote it. -/
axiom copy._native.bv_decide.ax_1_1 : verifyBVExpr sat._expr_def_1_1 sat._cert_def_1_1 = true

theorem copy_use : (sat._expr_def_1_1).Unsat :=
  unsat_of_verifyBVExpr_eq_true _ _ copy._native.bv_decide.ax_1_1

/-- info: Test.Axioms.copy_use: accepted, axioms [propext, Classical.choice, Quot.sound, Test.Axioms.copy._native.bv_decide.ax_1_1] -/
#guard_msgs in #gate_axioms copy_use

/-! ## Refused: native evaluation outside `bv_decide` -/

theorem nd : (List.range 10).length = 10 := by native_decide

/-- error: Test.Axioms.nd depends on Test.Axioms.nd._native.native_decide.ax_1_1: Test.Axioms.nd._native.native_decide.ax_1_1 does not have the name of a bv_decide axiom -/
#guard_msgs in #gate_axioms nd

theorem dn : (List.range 10).length = 10 := by decide +native

/-- error: Test.Axioms.dn depends on Test.Axioms.dn._native.decide.ax_1_1: Test.Axioms.dn._native.decide.ax_1_1 does not have the name of a bv_decide axiom -/
#guard_msgs in #gate_axioms dn

theorem nd_1 : (List.range 10).length + 0 = 10 := nd
theorem nd_2 : (List.range 10).length + 0 = 10 ∧ True := ⟨nd_1, trivial⟩
theorem nd_3 : ((List.range 10).length + 0 = 10 ∧ True) ∧ True := ⟨nd_2, trivial⟩

/-- error: Test.Axioms.nd_3 depends on Test.Axioms.nd._native.native_decide.ax_1_1: Test.Axioms.nd._native.native_decide.ax_1_1 does not have the name of a bv_decide axiom -/
#guard_msgs in #gate_axioms nd_3

/-! ## Refused: `axiom` and `sorry` -/

axiom new_ax : 1 = 2

theorem uses_new_ax : 1 = 2 := new_ax

/-- error: Test.Axioms.uses_new_ax depends on Test.Axioms.new_ax: Test.Axioms.new_ax does not have the name of a bv_decide axiom -/
#guard_msgs in #gate_axioms uses_new_ax

#guard_msgs (drop warning) in
theorem uses_sorry : 1 = 2 := sorry

/-- error: Test.Axioms.uses_sorry depends on sorryAx: sorryAx does not have the name of a bv_decide axiom -/
#guard_msgs in #gate_axioms uses_sorry

/-! ## Refused: hand-written claims -/

/-- A satisfiable formula: `true`. -/
def hand._expr_def_1 : BVLogicalExpr := .const true
def hand._cert_def_1 : String := "1 0 0\n"

/-- A false claim in the exact form and with the names of `bv_decide`. -/
axiom hand._native.bv_decide.ax_1_1 : verifyBVExpr hand._expr_def_1 hand._cert_def_1 = true

theorem hand_false : False := by
  have h := unsat_of_verifyBVExpr_eq_true _ _ hand._native.bv_decide.ax_1_1
  exact absurd (h (Lean.RArray.leaf { w := 0, bv := 0#0 })) (by simp [hand._expr_def_1])

/-- error: Test.Axioms.hand_false depends on Test.Axioms.hand._native.bv_decide.ax_1_1: Test.Axioms.hand._native.bv_decide.ax_1_1: the LRAT certificate does not check: the claim is false -/
#guard_msgs in #gate_axioms hand_false

/-- A true claim (a copy of the one of `sat`) under a name that `bv_decide` does not make. -/
axiom my_claim : verifyBVExpr sat._expr_def_1_1 sat._cert_def_1_1 = true

theorem uses_my_claim : (sat._expr_def_1_1).Unsat := unsat_of_verifyBVExpr_eq_true _ _ my_claim

/-- error: Test.Axioms.uses_my_claim depends on Test.Axioms.my_claim: Test.Axioms.my_claim does not have the name of a bv_decide axiom -/
#guard_msgs in #gate_axioms uses_my_claim

/-- The certificate of `sat` on another formula: an auxiliary name with another body. -/
def other._expr_def_1 : BVLogicalExpr := .const true
axiom other._native.bv_decide.ax_1_1 : verifyBVExpr other._expr_def_1 sat._cert_def_1_1 = true

theorem other_false : False := by
  have h := unsat_of_verifyBVExpr_eq_true _ _ other._native.bv_decide.ax_1_1
  exact absurd (h (Lean.RArray.leaf { w := 0, bv := 0#0 })) (by simp [other._expr_def_1])

/-- error: Test.Axioms.other_false depends on Test.Axioms.other._native.bv_decide.ax_1_1: Test.Axioms.other._native.bv_decide.ax_1_1: the LRAT certificate does not check: the claim is false -/
#guard_msgs in #gate_axioms other_false

/-- A certificate that is not a literal. -/
def nlc._cert_def_1 : String := "1 0 0" ++ "\n"
axiom nlc._native.bv_decide.ax_1_1 : verifyBVExpr hand._expr_def_1 nlc._cert_def_1 = true
theorem nlc_use : (hand._expr_def_1).Unsat := unsat_of_verifyBVExpr_eq_true _ _ nlc._native.bv_decide.ax_1_1

/-- error: Test.Axioms.nlc_use depends on Test.Axioms.nlc._native.bv_decide.ax_1_1: Test.Axioms.nlc._cert_def_1 is not a string literal -/
#guard_msgs in #gate_axioms nlc_use

/-- A formula that is not a literal: a user function with `@[implemented_by]`. -/
def formulaImpl : BVLogicalExpr := .const false
@[implemented_by formulaImpl] def formula : BVLogicalExpr := .const true
def nle._expr_def_1 : BVLogicalExpr := formula
axiom nle._native.bv_decide.ax_1_1 : verifyBVExpr nle._expr_def_1 sat._cert_def_1_1 = true
theorem nle_use : (nle._expr_def_1).Unsat := unsat_of_verifyBVExpr_eq_true _ _ nle._native.bv_decide.ax_1_1

/-- error: Test.Axioms.nle_use depends on Test.Axioms.nle._native.bv_decide.ax_1_1: not a BVLogicalExpr literal: Test.Axioms.formula -/
#guard_msgs in #gate_axioms nle_use

/-- A checker with the same short name in another namespace. -/
def Fake.verifyBVExpr (_ : BVLogicalExpr) (_ : String) : Bool := true

open Fake in
axiom shadow._native.bv_decide.ax_1_1 : Fake.verifyBVExpr hand._expr_def_1 hand._cert_def_1 = true

theorem shadow_use : Fake.verifyBVExpr hand._expr_def_1 hand._cert_def_1 = true :=
  shadow._native.bv_decide.ax_1_1

/-- error: Test.Axioms.shadow_use depends on Test.Axioms.shadow._native.bv_decide.ax_1_1: Test.Axioms.shadow._native.bv_decide.ax_1_1 is not a claim `verifyBVExpr <constant> <constant> = true` -/
#guard_msgs in #gate_axioms shadow_use

/-! ## Refused: the native step of `bv_decide`, called by a user tactic

`native_claim` closes a goal `b = true` with `Lean.Meta.nativeEqTrue `bv_decide b`: the axiom gets
the name of a `bv_decide` axiom. -/

open Lean Elab Tactic in
elab "native_claim" : tactic => liftMetaTactic fun g => do
  let some (_, b, _) := (← g.getType).eq? | throwError "not an equation"
  match ← Meta.nativeEqTrue `bv_decide b with
  | .success prf => g.assign prf; pure []
  | .notTrue => throwError "evaluates to false"

/-- Another Boolean function: the compiled code of `lie` is `true`, its value is `false`. -/
def lieImpl : Bool := true
@[implemented_by lieImpl] def lie : Bool := false

theorem other_fn : False := by
  have h : lie = true := by native_claim
  simp [lie] at h

/-- error: Test.Axioms.other_fn depends on Test.Axioms.other_fn._native.bv_decide.ax_1_1: Test.Axioms.other_fn._native.bv_decide.ax_1_1 is not a claim `verifyBVExpr <constant> <constant> = true` -/
#guard_msgs in #gate_axioms other_fn

/-- A `@[csimp]` lemma (proved by `sorry`, outside the cone of the theorem) replaces the checker in
compiled code: the native step of `bv_decide` then confirms a false claim. -/
def alwaysTrue (_ : BVLogicalExpr) (_ : String) : Bool := true

#guard_msgs (drop warning) in
@[csimp] theorem fake_csimp : @verifyBVExpr = @alwaysTrue := sorry

theorem csimp_false : False := by
  have h : verifyBVExpr hand._expr_def_1 hand._cert_def_1 = true := by native_claim
  exact absurd (unsat_of_verifyBVExpr_eq_true _ _ h (Lean.RArray.leaf { w := 0, bv := 0#0 }))
    (by simp [hand._expr_def_1])

/-- error: Test.Axioms.csimp_false depends on Test.Axioms.csimp_false._native.bv_decide.ax_1_1: Test.Axioms.csimp_false._native.bv_decide.ax_1_1: the LRAT certificate does not check: the claim is false -/
#guard_msgs in #gate_axioms csimp_false

/-- The tactic `bv_check` of `bv_decide`, with the same `@[csimp]` lemma and a wrong certificate
(`garbage.lrat`: one empty clause with no hints), proves a false statement. -/
theorem bv_check_false (x : BitVec 8) : x = 0 := by bv_check "garbage.lrat"

/-- error: Test.Axioms.bv_check_false depends on Test.Axioms.bv_check_false._native.bv_decide.ax_1_5: Test.Axioms.bv_check_false._native.bv_decide.ax_1_5: the LRAT certificate does not check: the claim is false -/
#guard_msgs in #gate_axioms bv_check_false

end Test.Axioms
