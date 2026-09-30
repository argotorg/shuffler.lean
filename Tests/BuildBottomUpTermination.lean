import Shuffler
import Batteries.Tactic.PrintOpaques

open Shuffler.BuildBottomUp

namespace BuildBottomUpTerminationTests

-- The public claim uses the actual StateT loop body and the initial state.
example (state : State source target spills) (inv : Invariant 0 state) :
    Acc (Continues (loopBody source target spills).val) ((none, 0), state) :=
  buildBottomUp_terminates state inv

private def countdown (_ : Unit) (cursor : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ)
  | 0 => .ok (.done cursor, 0)
  | remaining + 1 => .ok (.yield (cursor + 1), remaining)

-- Every execution must follow updates to both the control value and the state.
-- State zero exits on the first body call.
example (cursor remaining : ℕ) : Acc (Continues countdown) (cursor, remaining) := by
  induction remaining generalizing cursor with
  | zero =>
    constructor
    intro next step
    cases step
  | succ remaining ih =>
    constructor
    rintro ⟨next, state⟩ step
    have eq : (cursor + 1, remaining) = (next, state) := by
      simpa [Continues, countdown, StateT.run] using step
    cases eq
    exact ih (cursor + 1)

-- Error exits terminate, including assertions. Assertion exclusion is a separate claim.
example (err : Error) (cursor state : ℕ) :
    Acc (Continues (fun _ _ => fun _ : ℕ =>
      (.error err : Except Error (ForInStep ℕ × ℕ)))) (cursor, state) := by
  constructor
  intro next step
  cases step

private def errorAfterYield (_ : Unit) (cursor : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) :=
  fun state => if cursor = 0 then .ok (.yield 1, state + 1) else .error (.blocked 1)

-- An error after a successful continuation also ends every execution.
example (state : ℕ) : Acc (Continues errorAfterYield) (0, state) := by
  constructor
  rintro ⟨next, state'⟩ step
  have eq : (1, state + 1) = (next, state') := by
    simpa [Continues, errorAfterYield, StateT.run] using step
  cases eq
  constructor
  intro next step
  cases step

private def exitOrSpin (_ : Unit) (cursor : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) :=
  fun state => if state = 0 then .ok (.done (cursor + 7), state + 1)
    else .ok (.yield cursor, state)

private theorem noSelfStep {α : Type} {r : α → α → Prop} {current : α}
    (h : Acc r current) : ¬ r current current := by
  induction h with
  | intro current _ ih =>
    intro step
    exact ih current step step

-- Termination is required from the specified initial state, not from every state.
-- A done result can return different control and state values.
example (cursor : ℕ) : Acc (Continues exitOrSpin) (cursor, 0) := by
  constructor
  intro next step
  cases step

example (cursor : ℕ) : ¬ Acc (Continues exitOrSpin) (cursor, 1) := by
  intro h
  exact noSelfStep h rfl

private def spin (_ : Unit) (cursor : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) :=
  fun state => .ok (.yield cursor, state)

-- A loop that always continues at the same state cannot satisfy the claim.
example (cursor state : ℕ) : ¬ Acc (Continues spin) (cursor, state) := by
  intro h
  exact noSelfStep h rfl

private def grow (_ : Unit) (cursor : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) :=
  fun state => .ok (.yield (cursor + 1), state + 1)

-- An infinite execution need not repeat any configuration.
example (current : ℕ × ℕ) : ¬ Acc (Continues grow) current := by
  intro h
  induction h with
  | intro current _ ih => exact ih (current.1 + 1, current.2 + 1) rfl

-- A continuing step passes both updated values to any recursive continuation.
example (recur : ℕ → StateT ℕ (Except Error) ℕ) (cursor remaining : ℕ) :
    (repeatM.body (repeatStep countdown).val recur cursor).run (remaining + 1) =
      (recur (cursor + 1)).run remaining := by
  exact Continues.repeatM_body_eq countdown recur (cursor, remaining + 1)

-- A done result returns its updated values without using the continuation.
example (recur : ℕ → StateT ℕ (Except Error) ℕ) (cursor : ℕ) :
    (repeatM.body (repeatStep exitOrSpin).val recur cursor).run 0 =
      .ok (cursor + 7, 1) := by
  exact Continues.repeatM_body_eq exitOrSpin recur (cursor, 0)

-- Errors also bypass every continuation, including ones that would return success.
example (recur : ℕ → StateT ℕ (Except Error) ℕ) (err : Error) (cursor state : ℕ) :
    (repeatM.body (repeatStep (fun _ _ => fun _ : ℕ =>
      (.error err : Except Error (ForInStep ℕ × ℕ)))).val recur cursor).run state =
      .error err := by
  exact Continues.repeatM_body_eq _ recur (cursor, state)

/-- info: 'Shuffler.BuildBottomUp.Continues.repeatM_body_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Continues.repeatM_body_eq

-- A body containing another while loop must not pass that dependency check.
def bodyWithNestedLoop (_ : Unit) (control : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) := do
  while true do pure ()
  return .done control

/--
info: 'BuildBottomUpTerminationTests.bodyWithNestedLoop' depends on opaque or partial definitions: [Classical.choice,
 _private.Init.While.0.repeatM.impl]
-/
#guard_msgs in
#print opaques bodyWithNestedLoop

-- Partial code in a helper must also be detected. These functions are never evaluated.
partial def partialHelper (n : ℕ) : ℕ := partialHelper (n + 1)

def bodyWithPartialHelper (_ : Unit) (control : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) :=
  fun state => .ok (.done (partialHelper control), state)

/-- info: 'BuildBottomUpTerminationTests.bodyWithPartialHelper' depends on opaque or partial definitions: [BuildBottomUpTerminationTests.partialHelper] -/
#guard_msgs in
#print opaques bodyWithPartialHelper

end BuildBottomUpTerminationTests
