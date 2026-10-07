import Shuffler.Optimality.Schedule.Simulation
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

-- The existing prefix list can place the next frozen output. The remaining
-- sixteen positions retain every hard seed required by the original state.
theorem prefixes_place_boundary (spills : SpillSet) (stack target : Stack)
    (missing : Multiset Value) (h : Reserve spills stack target missing)
    (hne : missing ≠ 0) (hlarge : MAX_SWAP_DEPTH + 1 ≤ stack.length) :
    ∃ ops prepared, ops ∈ prefixes stack target ∧
      simulate spills stack ops = some prepared ∧ prepared.length = stack.length ∧
      prepared.take (frozen stack + 1) = target.take (frozen stack + 1) ∧
      (prepared : Multiset Value) = (stack : Multiset Value) ∧
      seeds spills missing ≤ (prepared.drop (frozen stack + 1) : Multiset Value) := by
  have hcard := congrArg Multiset.card h.1
  simp only [Multiset.card_add, Multiset.coe_card] at hcard
  have hpos : frozen stack < stack.length := by unfold frozen; omega
  have htpos : frozen stack < target.length := by omega
  let value := target[frozen stack]'htpos
  have htget : target[frozen stack]? = some value := List.getElem?_eq_getElem htpos
  have hboundary : boundary stack target missing = {value} := by
    unfold boundary
    rw [ite_eq_left ⟨hne, hlarge⟩, htget]
    rfl
  have hreserve : {value} + seeds spills missing ≤ (window stack : Multiset Value) := by
    simpa only [hboundary] using h.2.2
  have hvalue : value ∈ window stack := Multiset.mem_of_le hreserve (by simp)
  obtain ⟨offset, hoffset, hget⟩ := List.mem_drop_iff_getElem.mp hvalue
  let index := frozen stack + offset
  have hindex : index < stack.length := by dsimp [index]; omega
  change stack[index]'hindex = value at hget
  have horder : frozen stack ≤ index := by dsimp [index]; omega
  have hreach : stack.length ≤ frozen stack + (MAX_SWAP_DEPTH + 1) := by unfold frozen; omega
  let ops := if index = frozen stack then []
    else swapPosition stack index ++ swapPosition stack (frozen stack)
  let prepared := if index = frozen stack then stack else
    (stack.swap (stack.length - 1) index).swap (stack.length - 1) (frozen stack)
  have hsim : simulate spills stack ops = some prepared :=
    simulate_placement spills stack (frozen stack) index hpos hindex hreach horder
  have hlen : prepared.length = stack.length := by
    dsimp [prepared]
    split <;> simp only [List.length_swap]
  have hperm : prepared.Perm stack := by
    dsimp [prepared]
    split
    · exact List.Perm.refl _
    · exact (List.swap_perm _ _ _).trans (List.swap_perm _ _ _)
  have htop : stack.length - 1 < stack.length := by omega
  have hhead : prepared[frozen stack]'(by omega) = value := by
    dsimp [prepared]
    split
    next he => simpa only [he] using hget
    next =>
      rw [List.getElem_swap_right_of_lt (by simpa only [List.length_swap] using htop),
        List.getElem_swap_left_of_lt hindex]
      exact hget
  have hprefix : prepared.take (frozen stack) = stack.take (frozen stack) := by
    dsimp [prepared]
    split
    · rfl
    · rw [take_swap_of_le _ _ _ _ (by omega) (by omega),
        take_swap_of_le _ _ _ _ (by omega) horder]
  have hnextprefix : prepared.take (frozen stack + 1) = target.take (frozen stack + 1) := by
    rw [List.take_succ_eq_append_getElem (by omega),
      List.take_succ_eq_append_getElem htpos, hhead, hprefix, h.2.1]
  have hcounts := Multiset.coe_eq_coe.mpr hperm
  have hwindow : (prepared.drop (frozen stack) : Multiset Value) =
      (window stack : Multiset Value) := by
    apply add_left_cancel (a := (stack.take (frozen stack) : Multiset Value))
    calc
      (stack.take (frozen stack) : Multiset Value) + prepared.drop (frozen stack) =
          (prepared : Multiset Value) := by
        rw [← hprefix, Multiset.coe_add, List.take_append_drop]
      _ = (stack : Multiset Value) := hcounts
      _ = (stack.take (frozen stack) : Multiset Value) + window stack := by
        rw [Multiset.coe_add, window, List.take_append_drop]
  have hseeds : seeds spills missing ≤ (prepared.drop (frozen stack + 1) : Multiset Value) := by
    rw [← hwindow, List.drop_eq_getElem_cons (by omega), hhead] at hreserve
    exact (add_le_add_iff_left ({value} : Multiset Value)).mp hreserve
  refine ⟨ops, prepared, ?_, hsim, hlen, hnextprefix, hcounts, hseeds⟩
  have hplace : ops ∈ placements stack (frozen stack) value := by
    apply List.mem_map.mpr
    refine ⟨index, ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hindex, ?_⟩
    simp only [max_self, decide_eq_true_eq]
    exact ⟨horder, (List.getElem?_eq_getElem hindex).trans (congrArg some hget)⟩
  have hnot : ¬stack.length < MAX_SWAP_DEPTH + 1 := by omega
  simp only [prefixes, ite_eq_right hnot, htget]
  split
  · exact List.mem_append_left _ hplace
  · exact hplace

theorem prefixes_prepare (spills : SpillSet) (stack target : Stack)
    (missing : Multiset Value) (h : Reserve spills stack target missing) (hne : missing ≠ 0) :
    ∃ (ops : List Op) (fixed working tail : Stack), ops ∈ prefixes stack target ∧
      simulate spills stack ops = some (fixed ++ working) ∧ target = fixed ++ tail ∧
      working.length ≤ MAX_DUP_DEPTH + 1 ∧
      (fixed = [] ∨ working.length = MAX_DUP_DEPTH + 1) ∧
      (tail : Multiset Value) = (working : Multiset Value) + missing ∧
      seeds spills missing ≤ (working : Multiset Value) ∧
      frozen stack ≤ fixed.length ∧ fixed.length ≤ frozen stack + 1 := by
  by_cases hsmall : stack.length < MAX_SWAP_DEPTH + 1
  · have hf : frozen stack = 0 := by unfold frozen; omega
    refine ⟨[], [], stack, target, ?_, rfl, rfl, ?_, Or.inl rfl, h.1, ?_, ?_, ?_⟩
    · simp [prefixes, hsmall, swapPrefixes]
    · unfold MAX_SWAP_DEPTH MAX_DUP_DEPTH at *
      omega
    · have hg : ¬(missing ≠ 0 ∧ MAX_SWAP_DEPTH + 1 ≤ stack.length) := by omega
      simpa only [boundary, ite_eq_right hg, zero_add, window, hf, List.drop_zero] using h.2.2
    · simp [hf]
    · simp [hf]
  · have hlarge : MAX_SWAP_DEPTH + 1 ≤ stack.length := by omega
    obtain ⟨ops, prepared, hmem, hsim, hlen, hprefix, hcounts, hseeds⟩ :=
      prefixes_place_boundary spills stack target missing h hne hlarge
    let cut := frozen stack + 1
    let fixed := target.take cut
    let working := prepared.drop cut
    let tail := target.drop cut
    have hcard := congrArg Multiset.card h.1
    simp only [Multiset.card_add, Multiset.coe_card] at hcard
    have hcut : cut ≤ stack.length := by dsimp [cut, frozen]; omega
    have hfixed : fixed.length = cut := by
      simp only [fixed, List.length_take]
      omega
    have hworking : working.length = MAX_DUP_DEPTH + 1 := by
      simp only [working, List.length_drop, hlen, cut, frozen]
      unfold MAX_DUP_DEPTH MAX_SWAP_DEPTH at *
      omega
    have hp : prepared = fixed ++ working := by
      dsimp [fixed, working]
      rw [← hprefix]
      exact (List.take_append_drop _ _).symm
    have ht : target = fixed ++ tail := (List.take_append_drop _ _).symm
    have hb : (tail : Multiset Value) = (working : Multiset Value) + missing := by
      apply add_left_cancel (a := (fixed : Multiset Value))
      calc
        (fixed : Multiset Value) + tail = (target : Multiset Value) := by
          rw [Multiset.coe_add, ← ht]
        _ = (stack : Multiset Value) + missing := h.1
        _ = (prepared : Multiset Value) + missing := by rw [hcounts]
        _ = (fixed : Multiset Value) + ((working : Multiset Value) + missing) := by
          rw [hp, ← Multiset.coe_add, add_assoc]
    exact ⟨ops, fixed, working, tail, hmem, by simpa only [hp] using hsim, ht,
      hworking.le, Or.inr hworking, hb, hseeds, by rw [hfixed]; dsimp [cut]; omega,
      by rw [hfixed]⟩

end Shuffler.Optimality.Schedule
