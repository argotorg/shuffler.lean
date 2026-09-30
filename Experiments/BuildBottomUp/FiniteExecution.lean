import Experiments.BuildBottomUp.Checked

namespace BuildBottomUpExperiments.Checked

theorem loop_unfold (s : β) (f : Unit → β → M (ForInStep β)) :
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

-- Lean infers the body from the actual definition. The equality is checked
-- by the kernel; there is no second copy of the algorithm to maintain.
def loopParts (source target : Stack) (spills : SpillSet) :
    { body : Unit → Frame source target spills → M (ForInStep (Frame source target spills)) //
      ∀ cursor state, buildBottomUp cursor state = (do
        let frame ← forIn ({} : Lean.Loop) (none, state, cursor) body
        finishLoop frame) } := by
  exact ⟨_, by
    intro cursor state
    unfold buildBottomUp finishLoop
    dsimp only
    congr 2
    funext frame
    cases frame.1 <;> rfl⟩

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
    (h : LoopRuns body s r) : forIn ({} : Lean.Loop) s body = r := by
  induction h with
  | error he => rw [loop_unfold, he]; rfl
  | done hd => rw [loop_unfold, hd]; rfl
  | next hn _ ih => rw [loop_unfold, hn]; exact ih

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
      buildWith (fun frame => forIn ({} : Lean.Loop) frame (loopParts source target spills).val)
        cursor state := (loopParts source target spills).property cursor state

end BuildBottomUpExperiments.Checked
