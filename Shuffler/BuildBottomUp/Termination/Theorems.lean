import Shuffler.BuildBottomUp.Lemmas.Termination

open Std.Internal.Do

namespace Shuffler.BuildBottomUp

-- Every execution of the actual loop reaches an exit after finitely many steps.
-- Acc is the certificate used by Lean's well-founded recursion machinery.
-- Done and error results exit the loop; assertion errors are excluded below.
theorem buildBottomUp_terminates (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    Acc (Continues (loopParts source target spills).val) ((none, cursor), state) :=
  Lemmas.buildBottomUp_terminates cursor state inv

theorem buildBottomUp_triple (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    ⦃True⦄ buildBottomUp cursor state ⦃fun _ => True; allowedErrors⦄ := by
  rw [(loopParts source target spills).property cursor state]
  apply (spec_iff_triple _ _).mp
  have h := (build_action_triple (source := source) (target := target) (spills := spills) cursor).le_wp state inv
  have hs := (spec_iff_triple _ _).mpr (Triple.intro (fun (_ : True) => h))
  rw [StateT.run'_eq]
  exact hs.bind (fun _ _ => trivial)

theorem buildBottomUp_noAssertion (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) (reason : String) :
    buildBottomUp cursor state ≠ .error (.assertion reason) := by
  exact ((spec_iff_triple _ _).mpr (buildBottomUp_triple cursor state inv)).noAssertion reason

-- Assertion exclusion recovers the public error type.
private def restoreResult (result : Except Error α)
    (noAssertion : ∀ reason, result ≠ .error (.assertion reason)) : Except ShuffleErr α :=
  match result with
  | .ok value => .ok value
  | .error (.blocked excess) => .error (.Blocked excess)
  | .error (.assertion reason) => False.elim (noAssertion reason rfl)

def buildBottomUpVerified (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) : Except ShuffleErr ((res : Stack) × Trace spills source res) :=
  restoreResult (buildBottomUp cursor state) (buildBottomUp_noAssertion cursor state inv)

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_terminates

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_triple

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_noAssertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_noAssertion

/-- info: 'Shuffler.BuildBottomUp.buildBottomUpVerified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUpVerified

end Shuffler.BuildBottomUp
