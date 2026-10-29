import BbuBridge.Statements

/-!
The model loop is the original loop, by induction along the termination
measure of `Bbu.loop`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem loop_corr_aux (hs : StepStmt) (hf : FinishStmt) (e : Bbu.Env) (source : Stack)
    (st : Bbu.St) (state : OState e source) (t : Nat) (h : Rel e st state) :
    Corr ResRel (Bbu.loop e st t) (post (tgt e) (buildBottomUp.loop t state)) := by
  by_cases ht : t < e.n
  · have hc := hs e source st state t h ht
    cases hstep : Bbu.step e st t with
    | error err =>
      rw [hstep] at hc
      obtain ⟨err', heq, rfl⟩ := hc
      rw [Bbu.loop_error ht hstep, heq]
      rfl
    | ok r =>
      obtain ⟨st', nx⟩ := r
      cases nx with
      | next t' =>
        rw [hstep] at hc
        obtain ⟨state', h', heq⟩ := hc
        rw [Bbu.loop_next ht hstep, heq]
        exact loop_corr_aux hs hf e source st' state' t' h'
      | finish =>
        rw [hstep] at hc
        obtain ⟨h', heq⟩ := hc
        rw [Bbu.loop_finish ht hstep, heq]
        exact hf e source st' state h'
  · rw [Bbu.loop_ge ht, loop_ge t state (by rw [tgt_length]; omega)]
    by_cases hl : st.len = e.n
    · have hl' : state.stack.length = (tgt e).length := by rw [h.len, tgt_length, hl]
      rw [ite_eq_left hl]
      simp only [post, except_ok_bind, requires_of_true _ hl']
      exact ⟨h.stack, h.trace, h.canon⟩
    · have hl' : ¬ state.stack.length = (tgt e).length := by rw [h.len, tgt_length]; exact hl
      rw [ite_eq_right hl]
      simp only [post, except_ok_bind, requires, hl']
      rfl
termination_by (e.n - t, st.pendingGenerations)
decreasing_by
  rcases Bbu.step_progress hstep with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

theorem loop_corr (hs : StepStmt) (hf : FinishStmt) : LoopStmt :=
  loop_corr_aux hs hf

end BbuBridge
