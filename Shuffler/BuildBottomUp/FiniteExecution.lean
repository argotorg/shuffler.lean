import Experiments.BuildBottomUp.Checked
import Experiments.BuildBottomUp.ActionProofs

namespace BuildBottomUpExperiments.Checked

theorem loop_unfold [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m] (s : β) (f : Unit → β → m (ForInStep β)) :
    forIn ({} : Lean.Loop) s f = (do
      match ← f () s with
      | .done s => pure s
      | .yield s => forIn ({} : Lean.Loop) s f) :=
  Lean.Loop.forIn_eq_of_monadTail

abbrev Frame (source target : Stack) (spills : SpillSet) :=
  Option (Result source spills) × State source target spills × ℕ

def finishLoop (frame : Frame source target spills) : M (Result source spills) := do
  if let some result := frame.1 then
    return result
  ensure (frame.2.1.stack.length = target.length) "stack and target sizes differ"
  return ⟨frame.2.1.stack, frame.2.1.trace⟩

abbrev ControlFrame (source : Stack) (spills : SpillSet) :=
  Option (Result source spills) × ℕ

def finishAction (frame : ControlFrame source spills) : Action source target spills (Result source spills) := do
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
    (_ : Unit) (frame : Frame source target spills) : M (ForInStep (Frame source target spills)) := do
  let (step, state) ← (body () (frame.1, frame.2.2)).run frame.2.1
  return match step with
    | .done out => .done (out.1, state, out.2)
    | .yield out => .yield (out.1, state, out.2)

def runLoop (body : Unit → ControlFrame source spills → Action source target spills (ForInStep (ControlFrame source spills)))
    (frame : Frame source target spills) : M (Frame source target spills) := do
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
inductive LoopRuns (body : Unit → β → M (ForInStep β)) : β → M β → Prop where
  | error {s e} : body () s = .error e → LoopRuns body s (.error e)
  | done {s out} : body () s = .ok (.done out) → LoopRuns body s (.ok out)
  | next {s s' r} : body () s = .ok (.yield s') → LoopRuns body s' r → LoopRuns body s r

theorem loopRuns_iff (body : Unit → β → M (ForInStep β)) (s : β) (r : M β) :
    LoopRuns body s r ↔ match body () s with
      | .error e => r = .error e
      | .ok (.done out) => r = .ok out
      | .ok (.yield s') => LoopRuns body s' r := by
  constructor
  · intro h
    cases h with
    | error h => simp [h]
    | done h => simp [h]
    | next h next => simpa [h] using next
  · cases h : body () s with
    | error e => intro he; subst r; exact .error h
    | ok step =>
      cases step with
      | done out => intro he; subst r; exact .done h
      | yield s' => exact LoopRuns.next h

theorem LoopRuns.deterministic {body : Unit → β → M (ForInStep β)}
    (h : LoopRuns body s r) (h' : LoopRuns body s r') : r = r' := by
  induction h with
  | error he => have := (loopRuns_iff _ _ _).mp h'; symm; simpa [he] using this
  | done hd => have := (loopRuns_iff _ _ _).mp h'; symm; simpa [hd] using this
  | next hn _ ih =>
    apply ih
    have := (loopRuns_iff _ _ _).mp h'
    simpa [hn] using this

theorem LoopRuns.result_eq {body : Unit → β → M (ForInStep β)}
    (h : LoopRuns body s r) (loop : β → M β)
    (unfold_loop : ∀ s, loop s = (do
      match ← body () s with
      | .done out => pure out
      | .yield out => loop out)) : loop s = r := by
  induction h with
  | error he => rw [unfold_loop, he]; rfl
  | done hd => rw [unfold_loop, hd]; rfl
  | next hn _ ih => rw [unfold_loop, hn]; exact ih

-- A proof-only interpreter. On a path with no finite execution it returns the
-- chosen error. It obeys the same one-step equation as the real loop.
noncomputable def loopOr (fallback : Error) (body : Unit → β → M (ForInStep β))
    (s : β) : M β := by
  classical
  exact if h : ∃ r, LoopRuns body s r then Classical.choose h else .error fallback

theorem loopOr_of_runs (fallback : Error) {body : Unit → β → M (ForInStep β)}
    (h : LoopRuns body s r) : loopOr fallback body s = r := by
  unfold loopOr
  rw [dite_eq_left (show ∃ r, LoopRuns body s r from ⟨r, h⟩)]
  exact LoopRuns.deterministic (Classical.choose_spec _) h

theorem loopOr_unfold (fallback : Error) (body : Unit → β → M (ForInStep β)) (s : β) :
    loopOr fallback body s = (do
      match ← body () s with
      | .done out => pure out
      | .yield s' => loopOr fallback body s') := by
  cases h : body () s with
  | error e => rw [loopOr_of_runs fallback (.error h)]; rfl
  | ok step =>
    cases step with
    | done out => rw [loopOr_of_runs fallback (.done h)]; rfl
    | yield s' =>
      by_cases hex : ∃ r, LoopRuns body s' r
      · have hn := Classical.choose_spec hex
        rw [loopOr_of_runs fallback (LoopRuns.next h hn)]
        simpa only [bind, Except.bind] using (loopOr_of_runs fallback hn).symm
      · have hnone : ¬ ∃ r, LoopRuns body s r := by
          rintro ⟨r, hr⟩
          exact hex ⟨r, by simpa [h] using (loopRuns_iff _ _ _).mp hr⟩
        simp [loopOr, hex, hnone, bind, Except.bind]

def buildWith (loop : Frame source target spills → M (Frame source target spills))
    (cursor : ℕ) (state : State source target spills) : M (Result source spills) := do
  let frame ← loop (none, state, cursor)
  finishLoop frame

theorem buildBottomUp_as_loop (cursor : ℕ) (state : State source target spills) :
    buildBottomUp cursor state =
      buildWith (runLoop (loopParts source target spills).val) cursor state := by
  rw [(loopParts source target spills).property cursor state]
  unfold buildWith runLoop
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

end BuildBottomUpExperiments.Checked
