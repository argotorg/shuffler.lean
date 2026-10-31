import BbuBridge.Statements

/-!
One model step is one iteration of the original loop: the skip of a final
offset, the final permutation, or the urgent scan and one of four branches.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem step_corr (hu : UrgentStmt) (h1 : RestUrgentStmt) (h2 : RestTopStmt)
    (h3 : RestBoundStmt) (h4 : RestUnboundStmt) : StepStmt := by
  intro e source st state t h ht
  have htn : t < (tgt e).length := by rw [tgt_length]; exact ht
  unfold Bbu.step
  -- The offset is final.
  by_cases hfin : t < st.len ∧ st.dest t = t
  · rw [ite_eq_left hfin]
    have hl : t < state.stack.length := h.len ▸ hfin.1
    exact ⟨state, h, loop_skip t state htn hl ((h.isFinal ⟨t, hl⟩).mpr hfin.2)⟩
  rw [ite_eq_right hfin]
  have hnf : ¬ ∃ hl : t < state.stack.length, state.isFinal ⟨t, hl⟩ := by
    rintro ⟨hl, hf⟩
    exact hfin ⟨h.len ▸ hl, (h.isFinal ⟨t, hl⟩).mp hf⟩
  -- All is generated.
  by_cases hp : st.pendingGenerations = 0
  · rw [ite_eq_left hp]
    exact ⟨h, loop_finish t state htn hnf (h.pendingGenerations.trans hp)⟩
  rw [ite_eq_right hp, loop_rest t state htn hnf (h.pendingGenerations ▸ hp)]
  -- The urgent scan, then one of four branches.
  refine hu e source st state t _ (origRest t state) h fun u uo hc => ?_
  by_cases c4 : u ≠ e.n ∧ u ≠ t ∧ st.len < t + Bbu.MAX_SWAP_DEPTH
  · rw [ite_eq_left c4]
    exact h1 e source st state t u uo h (Nat.pos_of_ne_zero hp) ht hc c4
  rw [ite_eq_right c4]
  by_cases c5 : u = e.n ∧ t < st.len ∧ st.len < e.n ∧ Bbu.positionOf st st.len = none ∧
      st.len < t + Bbu.MAX_SWAP_DEPTH
  · rw [ite_eq_left c5]
    exact h2 e source st state t u uo h (Nat.pos_of_ne_zero hp) ht hc c4 c5
  rw [ite_eq_right c5]
  cases hb : Bbu.positionOf st t with
  | some b =>
    simp only [Option.isSome_some, ↓reduceIte]
    exact h3 e source st state t u uo b h ht hc c4 c5 hb
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact h4 e source st state t u uo h (Nat.pos_of_ne_zero hp) ht hc c4 c5 hb

end BbuBridge
