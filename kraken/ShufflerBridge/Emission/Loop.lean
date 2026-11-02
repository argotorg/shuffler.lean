module

public import ShufflerBridge.Emission.Statements
import all ShufflerBridge.Emission.Statements

@[expose] public section

/-!
The model loop is the original loop, by induction along the termination
measure of `FlatShuffler.loop`.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

theorem loop_corr_aux (hs : StepStmt) (hf : FinishStmt) (e : FlatShuffler.Env) (source : Stack)
    (st : FlatShuffler.St) (state : OState e source) (t : Nat) (h : Rel e st state) :
    ResCorr (Rel e) (FlatShuffler.loop FlatShuffler.finish e st t) (post (buildBottomUp.loop t state)) := by
  by_cases ht : t < e.n
  · have hc := hs e source st state t h ht
    cases hstep : FlatShuffler.step e st t with
    | error err =>
      rw [hstep] at hc
      rw [FlatShuffler.loop_error ht hstep]
      cases err with
      | blocked pos ex st' =>
        obtain ⟨state', h', heq⟩ := hc
        rw [heq, post_blocked]
        exact ⟨rfl, h'⟩
      | assertion =>
        obtain ⟨reason, heq⟩ := hc
        rw [heq, post_error]
        trivial
    | ok r =>
      obtain ⟨st', nx⟩ := r
      cases nx with
      | next t' =>
        rw [hstep] at hc
        obtain ⟨state', h', heq⟩ := hc
        rw [FlatShuffler.loop_next ht hstep, heq]
        exact loop_corr_aux hs hf e source st' state' t' h'
      | finish =>
        rw [hstep] at hc
        obtain ⟨h', heq⟩ := hc
        rw [FlatShuffler.loop_finish ht hstep, heq]
        exact hf e source st' state h'
  · rw [FlatShuffler.loop_ge ht, loop_ge t state (by rw [tgt_length]; omega)]
    by_cases hl : st.len = e.n
    · have hl' : state.stack.length = (decodedTargetStack e).length := by rw [h.len, tgt_length, hl]
      rw [ite_eq_left hl]
      simp only [post, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        requires_of_true _ hl']
      exact ⟨rfl, h⟩
    · have hl' : ¬ state.stack.length = (decodedTargetStack e).length := by rw [h.len, tgt_length]; exact hl
      rw [ite_eq_right hl]
      simp only [post, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        requires, hl']
      trivial
termination_by (e.n - t, st.pendingGenerations)
decreasing_by
  rcases FlatShuffler.step_progress hstep with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

theorem loop_corr (hs : StepStmt) (hf : FinishStmt) : LoopStmt :=
  loop_corr_aux hs hf

end ShufflerBridge.Emission
