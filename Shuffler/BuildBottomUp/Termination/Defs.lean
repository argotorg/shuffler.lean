import Shuffler.BuildBottomUp.Defs
import Batteries.Tactic.PrintOpaques

namespace Shuffler.BuildBottomUp

-- The four facts required at loop entry. The public theorem starts at cursor zero.
structure Invariant (cursor : ℕ) (state : State source target spills) : Prop where
  processed : ∀ i : Fin target.length, i.val < cursor → state.isFinal i
  size : state.stack.length + state.pending_generations = target.length
  pending : state.mapping.unmapped_target_slots = state.pending_generations
  available : ∀ i, state.isAvailable i

-- The pair Lean passes between iterations: optional return result and target offset.
-- StateT carries the shuffler state separately.
abbrev ControlFrame (source : Stack) (spills : SpillSet) :=
  Option ((res : Stack) × Trace spills source res) × ℕ

/-- `none` means no early return. `some r` stores the return result. -/
abbrev ControlFrame.result (frame : ControlFrame source spills) :
    Option ((res : Stack) × Trace spills source res) := frame.1

/-- The target offset carried to the next loop iteration. -/
abbrev ControlFrame.targetOffset (frame : ControlFrame source spills) : ℕ := frame.2

/-- After the loop, return the early result or check the final stack size. -/
def finishAction (frame : ControlFrame source spills) :
    Action source target spills ((res : Stack) × Trace spills source res) := do
  if let some result := frame.result then
    return result
  let state ← get
  ensure (state.stack.length = target.length) "stack and target sizes differ"
  return ⟨state.stack, state.trace⟩

/-- Extract the actual body, including the while condition.
The kernel checks the equality, including the initial control value and work after the loop. -/
def loopBody (source target : Stack) (spills : SpillSet) :
    { body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)) //
      ∀ state, buildBottomUp state = StateT.run' (do
        let frame ← forIn ({} : Lean.Loop) (none, 0) body
        finishAction frame) state } := by
  exact ⟨_, by
    intro state
    unfold buildBottomUp finishAction ControlFrame.result
    dsimp only
    congr 2
    funext frame
    cases frame.1 <;> rfl⟩

/--
All steps from `current` to `next` that continue the loop for another iteration.
Each pair contains the control value and the StateT state. Both returned values must match.
Only `.ok (.yield ...)` continues. Done and error results have no successor.
`next` comes first to match the argument order of `Acc`.
-/
def Continues {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (next current : β × σ) : Prop :=
  (body () current.1).run current.2 = .ok (.yield next.1, next.2)

/-- Extract the step function passed into repeatM by the same forIn invocation used in `loopBody` -/
def repeatStep {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β)) :
    { step : β → StateT σ (Except ε) (β ⊕ β) //
      ∀ initial, forIn ({} : Lean.Loop) initial body =
        (letI : Nonempty β := ⟨initial⟩; repeatM step initial) } := by
  exact ⟨_, by intro initial; rfl⟩

/-- `Continues` describes exactly the `.ok (.yield ...)` case below.
Only this case calls the next iteration, `recur`, with the returned control and state.
Done and error results exit. The equality holds for every `recur`. -/
theorem Continues.repeatM_body_eq {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (recur : β → StateT σ (Except ε) β) (current : β × σ) :
    (repeatM.body (repeatStep body).val recur current.1).run current.2 =
      match (body () current.1).run current.2 with
      | .ok (.yield control, state) => (recur control).run state
      | .ok (.done control, state) => .ok (control, state)
      | .error err => .error err := by
  cases h : body () current.1 current.2 with
  | error err => simp [repeatM.body, repeatStep, StateT.run, bind, StateT.bind, Except.bind, h]
  | ok result =>
    rcases result with ⟨step, state⟩
    cases step <;> simp [repeatM.body, repeatStep, StateT.run, bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure, h]

end Shuffler.BuildBottomUp
