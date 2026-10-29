import BbuBridge.Statements

/-!
The initial states: the model and the original start related, and `Mapped`
gives the condition of `buildBottomUp_correct_of_ok`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem initRel : InitRelStmt := by
  intro e source dests h
  have hl := h.length
  refine ⟨?_, ?_, ?_, rfl, Bbu.Pos_init h.length.symm h.dests, ?_, h.canonTarget⟩
  · show source.map decode = (List.zipWith Bbu.Slot.mk source dests).map fun s => decode s.val
    apply List.ext_getElem
    · simp [hl]
    · intro i h1 h2
      simp
  · intro i
    have hi : i.val < source.length := by
      have : i.val < (source.map decode).length := i.isLt
      simpa using this
    refine Option.map_eq_some_iff.mpr ⟨_, rfl, ?_⟩
    simp [Bbu.init, Bbu.St.dest, hi, hl]
  · show e.n - source.length = _
    rw [Bbu.init_pending h.length.symm h.dests, h.length]
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    simp only [Bbu.init, List.getElem_zipWith]
    exact h.canonSource _ (List.getElem_mem _)

theorem mapped : MappedStmt := by
  intro e source dests h hm i j hij
  have hi : i.val < source.length := by
    have : i.val < (source.map decode).length := i.isLt
    simpa using this
  have hi' : i.val < dests.length := by rw [h.length]; exact hi
  have hj : j.val = dests[i.val] := by
    simp only [initState, ofDests] at hij
    cases hij
    rfl
  have hj' : j.val < e.target.length := by simpa using j.isLt
  have := hm i.val hi hi'
  rw [← hj, List.getElem?_eq_getElem hj', Option.some_inj] at this
  show (source.map decode)[i.val] = (e.target.map decode)[j.val]
  simp [this]

end BbuBridge
