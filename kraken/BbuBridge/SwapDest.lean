import BbuBridge.Statements

/-!
`Bbu.swapDest` is `State.swapDestinations`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem swapDest_corr : SwapDestStmt := by
  intro e source st state a b h ha hb
  have hla : a < state.stack.length := h.len ▸ ha
  have hlb : b < state.stack.length := h.len ▸ hb
  have hsa : a < st.slots.length := ha
  have hsb : b < st.slots.length := hb
  refine ⟨{ state with mapping := state.mapping.swapDestinations ⟨a, hla⟩ ⟨b, hlb⟩ }, ?_, ?_⟩
  · unfold State.swapDestinations
    rw [show index state.stack.length a = .ok ⟨a, hla⟩ from index_eq ⟨a, hla⟩,
      show index state.stack.length b = .ok ⟨b, hlb⟩ from index_eq ⟨b, hlb⟩]
    rfl
  refine ⟨?_, ?_, h.pending, h.ops⟩
  · show state.stack = _
    rw [h.stack]
    apply List.ext_getElem
    · simp [Bbu.swapDest]
    · intro i h1 h2
      simp only [Bbu.swapDest, List.getElem_map, List.getElem_set]
      split_ifs with hib hia
      · subst hib; simp [Bbu.St.val, List.getElem?_eq_getElem hsb]
      · subst hia; simp [Bbu.St.val, List.getElem?_eq_getElem hsa]
      · rfl
  · intro i
    show (state.mapping.swapDestinations ⟨a, hla⟩ ⟨b, hlb⟩ i).map Fin.val = _
    rw [Mapping.swapDestinations_apply, h.dest]
    have hi : i.val < st.slots.length := h.slot_lt i
    simp only [Bbu.swapDest, Bbu.St.dest, List.getElem?_set, Equiv.swap_apply_def]
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

end BbuBridge
