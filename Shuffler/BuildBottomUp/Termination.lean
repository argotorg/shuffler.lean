import Shuffler.BuildBottomUp.Defs
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

def Processed
    (cursor : ℕ)
    (state : State source target spills) : Prop :=
  ∀ i : Fin target.length, i.val < cursor → state.isFinal i

-- The four facts required at each loop iteration.
structure Invariant (cursor : ℕ) (state : State source target spills) : Prop where
  processed : Processed cursor state
  size : state.stack.length + state.pending_generations = target.length
  pending : state.mapping.unmapped_target_slots = state.pending_generations
  available : ∀ i, state.isAvailable i

abbrev Frame (source target : Stack) (spills : SpillSet) :=
  Option ((res : Stack) × Trace spills source res) × State source target spills × ℕ

def finishLoop (frame : Frame source target spills) : Except Error ((res : Stack) × Trace spills source res) := do
  if let some result := frame.1 then
    return result
  ensure (frame.2.1.stack.length = target.length) "stack and target sizes differ"
  return ⟨frame.2.1.stack, frame.2.1.trace⟩

abbrev ControlFrame (source : Stack) (spills : SpillSet) :=
  Option ((res : Stack) × Trace spills source res) × ℕ

def finishAction (frame : ControlFrame source spills) :
    Action source target spills ((res : Stack) × Trace spills source res) := do
  if let some result := frame.1 then
    return result
  let state ← get
  ensure (state.stack.length = target.length) "stack and target sizes differ"
  return ⟨state.stack, state.trace⟩

-- Extract the actual StateT loop body; the kernel checks the equality.
def loopParts (source target : Stack) (spills : SpillSet) :
    { body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)) //
      ∀ cursor state, buildBottomUp cursor state = StateT.run' (do
        let frame ← forIn ({} : Lean.Loop) (none, cursor) body
        finishAction frame) state } := by
  exact ⟨_, by
    intro cursor state
    unfold buildBottomUp finishAction
    dsimp only
    congr 2
    funext frame
    cases frame.1 <;> rfl⟩

def loopStep (body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)))
    (_ : Unit) (frame : Frame source target spills) : Except Error (ForInStep (Frame source target spills)) := do
  let (step, state) ← (body () (frame.1, frame.2.2)).run frame.2.1
  return match step with
    | .done out => .done (out.1, state, out.2)
    | .yield out => .yield (out.1, state, out.2)

def runLoop (body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)))
    (frame : Frame source target spills) : Except Error (Frame source target spills) := do
  let (out, state) ← (forIn ({} : Lean.Loop) (frame.1, frame.2.2) body).run frame.2.1
  return (out.1, state, out.2)

-- A finite execution of the actual loop body, including an error exit.
inductive LoopRuns (body : Unit → β → Except Error (ForInStep β)) : β → Except Error β → Prop where
  | error {s e} : body () s = .error e → LoopRuns body s (.error e)
  | done {s out} : body () s = .ok (.done out) → LoopRuns body s (.ok out)
  | next {s s' r} : body () s = .ok (.yield s') → LoopRuns body s' r → LoopRuns body s r

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
    | .done out => .done (out.1, next, out.2)
    | .yield out => .yield (out.1, next, out.2))

-- The loop contract distinguishes continuation frames from exit frames.
def LoopInvariant : RepeatInvariant (ControlFrame source spills) (ControlFrame source spills)
    (State source target spills → Prop)
  | .inl frame, state => frame.1 = none ∧ Invariant frame.2 state
  | .inr frame, state => Spec (finishLoop (frame.1, state, frame.2)) (fun _ => True)

end Shuffler.BuildBottomUp
