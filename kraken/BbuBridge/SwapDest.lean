import BbuBridge.Statements

/-!
`Bbu.swapDestinations` is `State.swapDestinations`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The model and the original exchange the destinations of `a` and `b` in the same way.
theorem swapDest_rel {e : Bbu.Env} {source : Stack} {st : Bbu.St} {state : OState e source}
    (h : Rel e st state) (a b : Fin state.stack.length) :
    Rel e (Bbu.swapDestinations st a b) { state with mapping := state.mapping.swapDestinations a b } := by
  obtain ⟨a, hla⟩ := a
  obtain ⟨b, hlb⟩ := b
  dsimp only
  have ha : a < st.len := h.len ▸ hla
  have hb : b < st.len := h.len ▸ hlb
  have hsa : a < st.slots.length := ha
  have hsb : b < st.slots.length := hb
  refine ⟨?_, ?_, h.pendingGenerations, h.trace, h.pos.swapDest ha hb,
    canon_set (canon_set h.canon (h.canonVal a)) (h.canonVal b), h.target⟩
  · show state.stack = _
    rw [h.stack]
    apply List.ext_getElem
    · simp [Bbu.swapDestinations]
    · intro i h1 h2
      simp only [Bbu.swapDestinations, List.getElem_map, List.getElem_set]
      split_ifs with hib hia
      · subst hib; simp [Bbu.St.val, List.getElem?_eq_getElem hsb]
      · subst hia; simp [Bbu.St.val, List.getElem?_eq_getElem hsa]
      · rfl
  · intro i
    show (state.mapping.swapDestinations ⟨a, hla⟩ ⟨b, hlb⟩ i).map Fin.val = _
    rw [Mapping.swapDestinations_apply, h.dest]
    have hi : i.val < st.slots.length := h.slot_lt i
    simp only [Bbu.swapDestinations, Bbu.St.dest, List.getElem?_set, Equiv.swap_apply_def]
    by_cases hib : i.val = b
    · have : i = ⟨b, hlb⟩ := Fin.ext hib
      subst this
      by_cases hab : a = b
      · subst hab; simp [hi]
      · simp [hi, Ne.symm hab]
    · by_cases hia : i.val = a
      · have : i = ⟨a, hla⟩ := Fin.ext hia
        subst this
        have hba : b ≠ a := fun h' => hib (by simp [h'])
        simp [hi, hba, hsb]
      · simp [Fin.ext_iff, hia, hib, Ne.symm hia, Ne.symm hib]

theorem swapDest_corr : SwapDestStmt := by
  intro e source st state a b h ha hb
  have hla : a < state.stack.length := h.len ▸ ha
  have hlb : b < state.stack.length := h.len ▸ hb
  refine ⟨_, ?_, swapDest_rel h ⟨a, hla⟩ ⟨b, hlb⟩⟩
  unfold State.swapDestinations
  rw [show index state.stack.length a = .ok ⟨a, hla⟩ from index_eq ⟨a, hla⟩,
    show index state.stack.length b = .ok ⟨b, hlb⟩ from index_eq ⟨b, hlb⟩]
  rfl

end BbuBridge
