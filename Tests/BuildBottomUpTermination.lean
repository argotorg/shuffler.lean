import Shuffler

open Shuffler.BuildBottomUp

namespace BuildBottomUpTerminationTests

-- The public claim uses the actual StateT loop body and the initial state.
example (state : State source target spills) (inv : Invariant 0 state) :
    Acc (Continues (loopParts source target spills).val) ((none, 0), state) :=
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

end BuildBottomUpTerminationTests
