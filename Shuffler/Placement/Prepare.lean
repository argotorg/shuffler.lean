import Shuffler.Placement.Resources
import Shuffler.Placement.Permute

namespace Shuffler.Placement

-- Reserve one actual occurrence for the next fixed output, leaving separate
-- occurrences for every missing nonfree kind in the other sixteen slots.
theorem Reserve.prepare {spills : SpillSet} {source target : Stack} {missing : Multiset Value}
    (h : Reserve spills source target missing) (hmissing : missing ≠ 0)
    (hlarge : MAX_SWAP_DEPTH + 1 ≤ source.length) :
    ∃ fixed working tail : Stack,
      CanPlace spills source (fixed ++ working) 0 ∧
      target = fixed ++ tail ∧
      working.length ≤ MAX_DUP_DEPTH + 1 ∧
      (tail : Multiset Value) = (working : Multiset Value) + missing ∧
      seeds spills missing ≤ (working : Multiset Value) := by
  let f := frozen source
  have hcard := congrArg Multiset.card h.1
  simp only [Multiset.card_add, Multiset.coe_card] at hcard
  have hindex : f < target.length := by
    dsimp [f, frozen]
    unfold MAX_SWAP_DEPTH at hlarge ⊢
    omega
  let value := target[f]'hindex
  let oldFixed := source.take f
  let working := (window source).erase value
  let fixed := oldFixed ++ [value]
  let tail := target.drop (f + 1)
  have hboundary : boundary source target missing = {value} := by
    simp [boundary, hmissing, hlarge, f, value, List.getElem?_eq_getElem hindex]
  have hreserve : {value} + seeds spills missing ≤ (window source : Multiset Value) := by
    simpa only [hboundary] using h.2.2
  have hvalue : value ∈ window source :=
    Multiset.mem_of_le hreserve (by simp)
  have hperm : (window source).Perm (value :: working) := List.perm_cons_erase hvalue
  have hwindow : (window source : Multiset Value) = {value} + (working : Multiset Value) := by
    simpa only [Multiset.singleton_add, Multiset.cons_coe] using Multiset.coe_eq_coe.mpr hperm
  have hseeds : seeds spills missing ≤ (working : Multiset Value) := by
    rw [hwindow] at hreserve
    exact (add_le_add_iff_left ({value} : Multiset Value)).mp hreserve
  have hwindowLength : (window source).length = MAX_SWAP_DEPTH + 1 := by
    simp only [window, List.length_drop, frozen]
    omega
  have hworking : working.length ≤ MAX_DUP_DEPTH + 1 := by
    have he := List.length_erase_of_mem hvalue
    rw [hwindowLength] at he
    dsimp [working]
    unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
    omega
  have hsource : oldFixed ++ window source = source := List.take_append_drop f source
  have htarget : target = fixed ++ tail := by
    calc
      target = target.take f ++ target.drop f := (List.take_append_drop f target).symm
      _ = oldFixed ++ value :: tail := by
        rw [h.2.1, List.drop_eq_getElem_cons hindex]
      _ = fixed ++ tail := by simp only [fixed, List.append_assoc, List.singleton_append]
  have hpermFull : source.Perm (fixed ++ working) := by
    have hp := hperm.append_left oldFixed
    rw [hsource] at hp
    simpa only [fixed, List.append_assoc, List.singleton_append] using hp
  have hbalance : (tail : Multiset Value) = (working : Multiset Value) + missing := by
    have hb := h.1
    have ht : (target : Multiset Value) = (fixed : Multiset Value) + (tail : Multiset Value) := by
      rw [htarget]
      exact (Multiset.coe_add fixed tail).symm
    have hs : (source : Multiset Value) = (fixed : Multiset Value) + (working : Multiset Value) :=
      (Multiset.coe_eq_coe.mpr hpermFull).trans (Multiset.coe_add fixed working).symm
    rw [ht, hs, add_assoc] at hb
    exact add_left_cancel hb
  have hplace := canPlace_perm_append spills hperm oldFixed (by rw [hwindowLength])
  refine ⟨fixed, working, tail, ?_, htarget, hworking, hbalance, hseeds⟩
  simpa only [hsource, fixed, List.append_assoc, List.singleton_append] using hplace

end Shuffler.Placement
