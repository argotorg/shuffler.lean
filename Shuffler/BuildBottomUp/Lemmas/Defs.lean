import Shuffler.BuildBottomUp.Termination.Defs
import Std.Internal.Do

open Std.Internal.Do

namespace Shuffler.BuildBottomUp

-- A blocked operation is allowed. An assertion error is excluded.
def Spec (result : Except Error α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error (.blocked _) => True
  | .error (.assertion _) => False

-- The standard contracts use the same error policy as the result-level API.
def allowedErrors : EPost⟨Error → Prop⟩ :=
  epost⟨fun | .blocked _ => True | .assertion _ => False⟩

-- Project name for the proof tuple, which also contains the StateT state.
abbrev Frame (source target : Stack) (spills : SpillSet) :=
  Option ((res : Stack) × Trace spills source res) × State source target spills × ℕ

def finishLoop (frame : Frame source target spills) : Except Error ((res : Stack) × Trace spills source res) := do
  if let some result := frame.1 then
    return result
  ensure (frame.2.1.stack.length = target.length) "stack and target sizes differ"
  return ⟨frame.2.1.stack, frame.2.1.trace⟩

def loopStep (body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)))
    (_ : Unit) (frame : Frame source target spills) : Except Error (ForInStep (Frame source target spills)) := do
  let (step, state) ← (body () (frame.1, frame.2.2)).run frame.2.1
  return match step with
    | .done out => .done (out.result, state, out.targetOffset)
    | .yield out => .yield (out.result, state, out.targetOffset)

-- Compare the remaining target positions first, then the pending generations.
def terminationMeasure (cursor : ℕ) (state : State source target spills) : ℕ × ℕ :=
  (target.length - cursor, state.pending_generations)

def StepPost (cursor : ℕ) (state : State source target spills) :
    ForInStep (Frame source target spills) → Prop
  | .done out => Spec (finishLoop out) (fun _ => True)
  | .yield out => out.1 = none ∧ Invariant out.2.2 out.2.1 ∧
      Prod.Lex Nat.lt Nat.lt (terminationMeasure out.2.2 out.2.1)
        (terminationMeasure cursor state)

def BodyPost (cursor : ℕ) (state : State source target spills)
    (step : ForInStep (ControlFrame source spills)) (next : State source target spills) : Prop :=
  StepPost cursor state (match step with
    | .done out => .done (out.result, next, out.targetOffset)
    | .yield out => .yield (out.result, next, out.targetOffset))

-- The loop contract distinguishes continuation frames from exit frames.
def LoopInvariant : RepeatInvariant (ControlFrame source spills) (ControlFrame source spills)
    (State source target spills → Prop)
  | .inl frame, state => frame.result = none ∧ Invariant frame.targetOffset state
  | .inr frame, state => Spec (finishLoop (frame.result, state, frame.targetOffset)) (fun _ => True)

end Shuffler.BuildBottomUp
