import Shuffler.Placement.Completion
import Shuffler.Placement.Prepare

namespace Shuffler.Placement

theorem Reserve.canPlace (h : Reserve spills source target missing) :
    CanPlace spills source target missing := by
  by_cases hz : missing = 0
  · subst missing
    apply canPlace_perm_of_take_eq spills source target (frozen source)
    · exact (Multiset.coe_eq_coe.mp (by simpa using h.1)).symm
    · exact h.2.1.symm
    · unfold frozen
      omega
  by_cases hs : source.length ≤ MAX_DUP_DEPTH + 1
  · have hf : frozen source = 0 := by
      unfold frozen MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have hl : ¬MAX_SWAP_DEPTH + 1 ≤ source.length := by
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    have hseeds : seeds spills missing ≤ (source : Multiset Value) := by
      simpa [boundary, window, hf, hl] using h.2.2
    simpa only [List.nil_append] using
      canPlace_complete spills [] source target missing hs h.1 hseeds
  · have hl : MAX_SWAP_DEPTH + 1 ≤ source.length := by
      unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    obtain ⟨fixed, working, tail, hfirst, htarget, hsmall, hbalance, hseeds⟩ :=
      h.prepare hz hl
    rw [htarget]
    simpa only [zero_add] using hfirst.trans
      (canPlace_complete spills fixed working tail missing hsmall hbalance hseeds)

end Shuffler.Placement
