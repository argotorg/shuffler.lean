import Shuffler.BuildBottomUp.Defs

namespace Shuffler.BuildBottomUp

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

-- Project name for the pair that Lean passes between loop iterations.
abbrev ControlFrame (source : Stack) (spills : SpillSet) :=
  Option ((res : Stack) × Trace spills source res) × ℕ

/-- The result of an early return, if one has occurred. -/
abbrev ControlFrame.result (frame : ControlFrame source spills) :
    Option ((res : Stack) × Trace spills source res) := frame.1

/-- The target offset carried to the next loop iteration. -/
abbrev ControlFrame.targetOffset (frame : ControlFrame source spills) : ℕ := frame.2

def finishAction (frame : ControlFrame source spills) :
    Action source target spills ((res : Stack) × Trace spills source res) := do
  if let some result := frame.result then
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
    unfold buildBottomUp finishAction ControlFrame.result
    dsimp only
    congr 2
    funext frame
    cases frame.1 <;> rfl⟩

/-- One body call yields the next control value and state.
The next configuration comes first, as required by `Acc`.
Done and error results have no successor in this relation. -/
def Continues {σ β ε : Type}
    (body : Unit → β → StateT σ (Except ε) (ForInStep β))
    (next current : β × σ) : Prop :=
  (body () current.1).run current.2 = .ok (.yield next.1, next.2)

end Shuffler.BuildBottomUp
