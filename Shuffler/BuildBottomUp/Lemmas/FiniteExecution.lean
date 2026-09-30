import Shuffler.BuildBottomUp.Lemmas.Action
import Shuffler.BuildBottomUp.Termination.Defs

namespace Shuffler.BuildBottomUp

theorem loop_unfold [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m] (s : β) (f : Unit → β → m (ForInStep β)) :
    forIn ({} : Lean.Loop) s f = (do
      match ← f () s with
      | .done s => pure s
      | .yield s => forIn ({} : Lean.Loop) s f) :=
  Lean.Loop.forIn_eq_of_monadTail

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
