import Shuffler.BuildBottomUp.Lemmas.Termination
import Shuffler.BuildBottomUp.Lemmas.Continues

open Std.Internal.Do

namespace Shuffler.BuildBottomUp

/-- `Continues body next current` describes a step from `current` to `next`.
Each pair is `(control, state)`. Read `↔` as "if and only if".
The right side says Lean's step continues (`.inl`) with the control and state in `next`. -/
theorem Continues.iff_repeatStep {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (next current : β × σ) :
    Continues body next current ↔
      ((Continues.repeatStep body).val current.1).run current.2 = .ok (.inl next.1, next.2) :=
  Lemmas.continues_iff_repeatStep body next current

/-- The left side runs one loop step from `current = (control, state)`.
The right side lists the three cases. `recur` is the function for the next iteration.
`.yield` calls `recur` with both new values. `.done` and `.error` exit without calling it. -/
theorem Continues.repeatM_body_eq {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (recur : β → StateT σ (Except ε) β) (current : β × σ) :
    (repeatM.body (Continues.repeatStep body).val recur current.1).run current.2 =
      match (body () current.1).run current.2 with
      | .ok (.yield control, state) => (recur control).run state
      | .ok (.done control, state) => .ok (control, state)
      | .error err => .error err :=
  Lemmas.repeatM_body_eq body recur current

/-- No infinite chain of continuing steps starts at `((none, 0), state)`.
Runtime termination also requires each body call to finish; see README.md.
Errors count as exits. Exclusion of assertion errors is proved separately below. -/
theorem buildBottomUp_terminates (state : State source target spills)
    (inv : Invariant 0 state) :
    Acc (Continues (loopBody source target spills).val) ((none, 0), state) :=
  Lemmas.loop_terminates 0 state inv

/-- Only allowed errors can be returned. This claim does not establish runtime termination. -/
theorem buildBottomUp_triple (state : State source target spills)
    (inv : Invariant 0 state) :
    ⦃True⦄ buildBottomUp state ⦃fun _ => True; allowedErrors⦄ := by
  rw [(loopBody source target spills).property state]
  apply (spec_iff_triple _ _).mp
  have h := (build_action_triple (source := source) (target := target) (spills := spills) 0).le_wp state inv
  have hs := (spec_iff_triple _ _).mpr (Triple.intro (fun (_ : True) => h))
  rw [StateT.run'_eq]
  exact hs.bind (fun _ _ => trivial)

/-- Under the input invariant, no returned error is an assertion error. -/
theorem buildBottomUp_noAssertion (state : State source target spills)
    (inv : Invariant 0 state) (reason : String) :
    buildBottomUp state ≠ .error (.assertion reason) := by
  exact ((spec_iff_triple _ _).mpr (buildBottomUp_triple state inv)).noAssertion reason

-- Use the proof to remove the assertion case from the error type.
private def restoreResult (result : Except Error α)
    (noAssertion : ∀ reason, result ≠ .error (.assertion reason)) : Except ShuffleErr α :=
  match result with
  | .ok value => .ok value
  | .error (.blocked excess) => .error (.Blocked excess)
  | .error (.assertion reason) => False.elim (noAssertion reason rfl)

/-- Run buildBottomUp and return only errors in the public error type.
The invariant is a proof argument; it is not a runtime check. -/
def buildBottomUpVerified (state : State source target spills)
    (inv : Invariant 0 state) : Except ShuffleErr ((res : Stack) × Trace spills source res) :=
  restoreResult (buildBottomUp state) (buildBottomUp_noAssertion state inv)

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
