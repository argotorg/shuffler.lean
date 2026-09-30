import Shuffler.BuildBottomUp.LoopProofs

open Std.Internal.Do

namespace Shuffler.BuildBottomUp

-- Each continuation of the actual loop decreases the lexicographic measure.
theorem buildBottomUp_total (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    ∃ r, LoopRuns (loopStep (loopParts source target spills).val) (none, state, cursor) r ∧
      Spec (r >>= finishLoop) (fun _ => True) := by
  have hs := loop_step_spec cursor state inv
  cases heq : (loopStep (loopParts source target spills).val) () (none, state, cursor) with
  | error err =>
    obtain ⟨excess, rfl⟩ := hs.error heq
    exact ⟨.error (.blocked excess), .error heq, True.intro⟩
  | ok step =>
    have hp : StepPost cursor state step := by simpa only [heq, Spec] using hs
    cases step with
    | done out => exact ⟨.ok out, .done heq, hp⟩
    | yield out =>
      obtain ⟨result, next, cursor'⟩ := out
      obtain ⟨rfl, hi, hlt⟩ := hp
      obtain ⟨r, hr, hs⟩ := buildBottomUp_total cursor' next hi
      exact ⟨r, .next heq hr, hs⟩
termination_by (target.length - cursor, state.pending_generations)
decreasing_by exact hlt

theorem buildBottomUp_terminates (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    ∃ r, LoopRuns (loopStep (loopParts source target spills).val) (none, state, cursor) r := by
  obtain ⟨r, hr, _⟩ := buildBottomUp_total cursor state inv
  exact ⟨r, hr⟩

theorem buildBottomUp_eq_of_loopRuns (cursor : ℕ) (state : State source target spills)
    {r : M (Frame source target spills)}
    (h : LoopRuns (loopStep (loopParts source target spills).val) (none, state, cursor) r) :
    buildBottomUp cursor state = (r >>= finishLoop) := by
  rw [buildBottomUp_as_loop, h.result_eq]

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
private def restoreResult (result : M α)
    (noAssertion : ∀ reason, result ≠ .error (.assertion reason)) : Except ShuffleErr α :=
  match result with
  | .ok value => .ok value
  | .error (.blocked excess) => .error (.Blocked excess)
  | .error (.assertion reason) => False.elim (noAssertion reason rfl)

def buildBottomUpVerified (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) : Except ShuffleErr ((res : Stack) × Trace spills source res) :=
  restoreResult (buildBottomUp cursor state) (buildBottomUp_noAssertion cursor state inv)

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_total

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
