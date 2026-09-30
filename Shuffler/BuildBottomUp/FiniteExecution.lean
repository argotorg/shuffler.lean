import Shuffler.BuildBottomUp.ActionProofs

namespace Shuffler.BuildBottomUp

theorem loop_unfold [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m] (s : β) (f : Unit → β → m (ForInStep β)) :
    forIn ({} : Lean.Loop) s f = (do
      match ← f () s with
      | .done s => pure s
      | .yield s => forIn ({} : Lean.Loop) s f) :=
  Lean.Loop.forIn_eq_of_monadTail

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

theorem runLoop_unfold (body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)))
    (frame : Frame source target spills) :
    runLoop body frame = (do
      match ← loopStep body () frame with
      | .done out => pure out
      | .yield next => runLoop body next) := by
  unfold runLoop loopStep
  conv_lhs => rw [loop_unfold]
  simp only [StateT.run_bind]
  cases h : (body () (frame.1, frame.2.2)).run frame.2.1 with
  | error e => rfl
  | ok result => obtain ⟨step, state⟩ := result; cases step <;> rfl

-- A finite execution of the actual loop body, including an error exit.
inductive LoopRuns (body : Unit → β → Except Error (ForInStep β)) : β → Except Error β → Prop where
  | error {s e} : body () s = .error e → LoopRuns body s (.error e)
  | done {s out} : body () s = .ok (.done out) → LoopRuns body s (.ok out)
  | next {s s' r} : body () s = .ok (.yield s') → LoopRuns body s' r → LoopRuns body s r

theorem LoopRuns.result_eq
    {body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills))}
    {frame : Frame source target spills} {r : Except Error (Frame source target spills)}
    (h : LoopRuns (loopStep body) frame r) : runLoop body frame = r := by
  induction h with
  | error he => rw [runLoop_unfold, he]; rfl
  | done hd => rw [runLoop_unfold, hd]; rfl
  | next hn _ ih => rw [runLoop_unfold, hn]; exact ih

theorem buildBottomUp_as_loop (cursor : ℕ) (state : State source target spills) :
    buildBottomUp cursor state =
      (runLoop (loopParts source target spills).val (none, state, cursor) >>= finishLoop) := by
  rw [(loopParts source target spills).property cursor state]
  unfold runLoop
  simp only [StateT.run'_eq, StateT.run_bind]
  cases h : (forIn ({} : Lean.Loop) (none, cursor) (loopParts source target spills).val).run state with
  | error e => rfl
  | ok frame =>
    obtain ⟨⟨result, cursor⟩, next⟩ := frame
    cases result with
    | some result => rfl
    | none =>
      simp only [except_ok_bind, pure_bind, finishAction, finishLoop,
        Action.run_get, Action.run_lift, StateT.run_pure]
      cases ensure (next.stack.length = target.length) "stack and target sizes differ" <;> rfl

end Shuffler.BuildBottomUp
