import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.Permute.Theorems
import Shuffler.BuildBottomUp.Theorems.Feasibility.Defs

namespace Shuffler.Optimality.BBU

open Shuffler.Permute

theorem two_mul_cyclesAway_le_support {ι : Type} [Fintype ι] [DecidableEq ι]
    (perm : Equiv.Perm ι) (top : ι) :
    2 * (Permutation.cyclesAwayFromTop perm top).card ≤ (perm.support.erase top).card := by
  have h := Permutation.two_mul_card_cycles_le_support perm
  by_cases ht : perm top = top
  · rw [Permutation.cyclesAwayFromTop_of_fixed perm top ht]
    simpa [Equiv.Perm.mem_support, ht] using h
  · rw [Permutation.cyclesAwayFromTop_eq_erase]
    have hs := Finset.card_erase_add_one (Equiv.Perm.mem_support.mpr ht)
    have hc := Finset.card_erase_add_one
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr ht))
    omega

private theorem reachable_support_card (source : Stack) (perm : Permutation source)
    (hne : 0 < source.length) (h : all_swaps_reachable perm) :
    (perm.support.erase ⟨source.length - 1, by omega⟩).card ≤ MAX_SWAP_DEPTH := by
  let top : Fin source.length := ⟨source.length - 1, by omega⟩
  have hcard := Finset.card_le_card_of_injOn (s := perm.support.erase top)
    (t := Finset.range MAX_SWAP_DEPTH) (fun i : Fin source.length => i.rev.val - 1) ?_ ?_
  · simpa using hcard
  · intro i hi
    have hi' := Finset.mem_erase.mp hi
    have hr := h i hi'.2
    have hne := Fin.val_ne_of_ne hi'.1
    simp only [Finset.mem_coe, Finset.mem_range, Fin.rev]
    dsimp [top] at hne
    have := i.isLt
    dsimp [Fin.rev] at hr
    omega
  · intro i hi j hj hij
    have hi' := Finset.mem_erase.mp hi
    have hj' := Finset.mem_erase.mp hj
    have hi_ne := Fin.val_ne_of_ne hi'.1
    have hj_ne := Fin.val_ne_of_ne hj'.1
    dsimp [top] at hi_ne hj_ne
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    dsimp [Fin.rev] at hij
    omega

private theorem support_card_le_length (source : Stack) (perm : Permutation source)
    (hne : 0 < source.length) :
    (perm.support.erase ⟨source.length - 1, by omega⟩).card ≤ source.length - 1 := by
  have h := Finset.card_le_card
    (Finset.erase_subset_erase ⟨source.length - 1, by omega⟩ (Finset.subset_univ perm.support))
  simpa using h

theorem permute_swapCount_le_window (spills : SpillSet) (source : Stack)
    (perm : Permutation source) {result : Stack} {trace : Trace spills source result}
    (hrun : permute spills source perm = .ok ⟨result,trace⟩) :
    trace.swapCount ≤ permuteSwapBound source.length := by
  by_cases hne : 0 < source.length
  · have hr : all_swaps_reachable perm := by
      by_contra hn
      obtain ⟨_, he, _⟩ := permute_blocks_unreachable spills source perm hn
      rw [hrun] at he
      cases he
    rw [permute_swapCount spills source perm hne hrun]
    have hs := reachable_support_card source perm hne hr
    have hl := support_card_le_length source perm hne
    have hc := two_mul_cyclesAway_le_support perm ⟨source.length - 1, by omega⟩
    unfold Permutation.swapCount permuteSwapBound
    dsimp only
    omega
  · rw [permute, dite_eq_right hne] at hrun
    cases hrun
    simp [Trace.swapCount]

-- Permute never appends a POP or a birth operation.
theorem permute_noPop (spills : SpillSet) (source : Stack)
    (perm : Permutation source) {result : Stack} {trace : Trace spills source result}
    (hrun : permute spills source perm = .ok ⟨result,trace⟩) : trace.noPop := by
  by_cases hne : 0 < source.length
  · rw [permute, dite_eq_left hne] at hrun
    have hgo := permute.go.induct spills source hne
      (motive := fun current remaining before hlen =>
        ∀ {result : Stack} {after : Trace spills source result},
          permute.go spills source current remaining before hne hlen = .ok ⟨result,after⟩ →
            before.noPop → after.noPop)
      ?_ ?_ ?_ ?_ ?_ source perm (.Lit source) rfl hrun trivial
    · exact hgo
    · intro current perm before hlen top htop ht idx hdepth result after hresult
      rw [permute.go.eq_1, dite_eq_left ht, dite_eq_left hdepth] at hresult
      contradiction
    · intro current perm before hlen top htop ht idx hdepth stack' perm' h1 h2 h3 trace' ih
        result after hresult hp
      rw [permute.go.eq_1, dite_eq_left ht, dite_eq_right hdepth] at hresult
      exact ih hresult hp
    · intro current perm before hlen top htop ht search pos hpos hsearch idx hdepth
        result after hresult
      dsimp only [search, idx] at hsearch hdepth
      rw [permute.go.eq_1, dite_eq_right ht] at hresult
      simp only [hsearch, dite_eq_left hdepth] at hresult
      contradiction
    · intro current perm before hlen top htop ht search pos hpos hsearch idx hdepth hpos_ne hlt
        stack' perm' h1 h2 h3 trace' ih result after hresult hp
      dsimp only [search, idx] at hsearch hdepth
      rw [permute.go.eq_1, dite_eq_right ht] at hresult
      simp only [hsearch, dite_eq_right hdepth] at hresult
      exact ih hresult hp
    · intro current perm before hlen top htop ht search hsearch result after hresult hp
      dsimp only [search] at hsearch
      rw [permute.go.eq_1, dite_eq_right ht, hsearch] at hresult
      cases hresult
      exact hp
  · rw [permute, dite_eq_right hne] at hrun
    cases hrun
    trivial

end Shuffler.Optimality.BBU
