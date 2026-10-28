import BbuBridge.Statements

/-!
The expected stack of the initial original state is `expected`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem expected_eq : ExpectedStmt := by
  intro e source dests h
  have hl := h.length
  have hsl : (initState e source dests h).stack.length = source.length := by simp [initState]
  -- The slot at `i` is bound for `d` if and only if `dests[i] = d`.
  have hsym : ∀ (d : Fin (tgt e).length) (i : Fin (initState e source dests h).stack.length),
      (initState e source dests h).mapping.symm d = some i ↔
        dests[i.val]'(by have := i.isLt; omega) = d.val := by
    intro d i
    rw [PEquiv.eq_some_iff]
    exact ⟨fun h => congrArg Fin.val (Option.some_injective _ h), fun h => congrArg some (Fin.ext h)⟩
  apply List.ext_getElem
  · simp [State.expectedStack, expected, Bbu.Env.n]
  intro d h1 h2
  simp only [State.expectedStack, List.getElem_ofFn, expected, List.getElem_map, List.getElem_range]
  have hd : d < (tgt e).length := by simpa [State.expectedStack] using h1
  cases hs : (initState e source dests h).mapping.symm ⟨d, hd⟩ with
  | some pos =>
    -- `pos` is the first (and only) index of `d` in `dests`.
    have hp := (hsym ⟨d, hd⟩ pos).mp hs
    have hpos : pos.val < source.length := by have := pos.isLt; omega
    have hi : dests.idxOf? d = some pos.val := by
      rw [List.idxOf?_eq_some_iff]
      refine ⟨by omega, hp, fun j hj hjd => ?_⟩
      have := h.dests.2 j (by omega) pos (by omega) (hjd.trans hp.symm)
      omega
    simp only [hi, getElem!_pos source pos.val hpos]
    exact List.getElem_map _
  | none =>
    -- `d` is not in `dests`.
    have hn : dests.idxOf? d = none := by
      rw [List.idxOf?_eq_none_iff]
      intro hm
      obtain ⟨i, hi, hid⟩ := List.getElem_of_mem hm
      have := (hsym ⟨d, hd⟩ ⟨i, by omega⟩).mpr hid
      rw [hs] at this
      cases this
    simp only [hn]
    exact tgt_get e d hd

end BbuBridge
