import Shuffler.Permute.Optimality
import Mathlib.Data.Finset.Max

namespace Shuffler.Optimality.BirthPlacement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- A strict rank increase prevents a cycle from lying wholly inside selected.
-- Each cycle must spend at least one of its positions outside that set.
theorem selected_card_le_arbitrarySwapCount (perm : Equiv.Perm ι)
    (selected : Finset ι) (rank : ι → Nat)
    (hstep : ∀ index ∈ selected, perm index ∈ selected → rank index < rank (perm index)) :
    selected.card ≤ Shuffler.Permute.Permutation.arbitrarySwapCount perm := by
  have hsupport : selected ⊆ perm.support := by
    intro index hi
    apply Equiv.Perm.mem_support.mpr
    intro he
    have hp : perm index ∈ selected := by simpa only [he] using hi
    have := hstep index hi hp
    rw [he] at this
    omega
  have houtside : ∀ cycle ∈ perm.cycleFactorsFinset,
      ∃ index ∈ cycle.support, index ∉ selected := by
    intro cycle hc
    by_contra! hall
    obtain ⟨index, hi, hmax⟩ := Finset.exists_max_image cycle.support rank
      (Equiv.Perm.IsCycle.nonempty_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1)
    have hp := (Equiv.Perm.mem_cycleFactorsFinset_support hc index).mpr hi
    have := hstep index (hall index hi) (hall (perm index) hp)
    have := hmax (perm index) hp
    omega
  have hcycles : perm.cycleFactorsFinset.card ≤ (perm.support \ selected).card := by
    apply Finset.card_le_card_of_surjOn perm.cycleOf
    intro cycle hc
    obtain ⟨index, hi, hn⟩ := houtside cycle hc
    refine ⟨index, Finset.mem_sdiff.mpr
      ⟨Equiv.Perm.mem_cycleFactorsFinset_support_le hc hi, hn⟩, ?_⟩
    exact ((Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff perm cycle hc index).mpr hi).symm
  have hcard := Finset.card_sdiff_add_card_eq_card hsupport
  unfold Shuffler.Permute.Permutation.arbitrarySwapCount
  omega

theorem selected_card_le_swaps_length (perm : Equiv.Perm ι)
    (selected : Finset ι) (rank : ι → Nat)
    (hstep : ∀ index ∈ selected, perm index ∈ selected → rank index < rank (perm index))
    (swaps : List (ι × ι))
    (hprod : (swaps.map (fun pair => Equiv.swap pair.1 pair.2)).prod = perm) :
    selected.card ≤ swaps.length :=
  (selected_card_le_arbitrarySwapCount perm selected rank hstep).trans
    (Shuffler.Permute.Permutation.arbitrarySwapCount_le_length_swaps perm swaps hprod)

-- The values can have repeated copies. Only the value at each endpoint matters.
-- Every selected mismatch decreases the value rank, so selected edges cannot
-- form a complete permutation cycle on their own.
theorem value_rank_card_le_arbitrarySwapCount {α : Type*}
    (source target : ι → α) (perm : Equiv.Perm ι)
    (hcompatible : ∀ index, source index = target (perm index))
    (selected : Finset ι) (rank : α → Nat)
    (hdecrease : ∀ index ∈ selected, rank (target index) < rank (source index)) :
    selected.card ≤ Shuffler.Permute.Permutation.arbitrarySwapCount perm := by
  apply selected_card_le_arbitrarySwapCount perm selected (fun index => rank (target index))
  intro index hi _
  rw [← hcompatible index]
  exact hdecrease index hi

theorem value_rank_card_le_swaps_length {α : Type*}
    (source target : ι → α) (perm : Equiv.Perm ι)
    (hcompatible : ∀ index, source index = target (perm index))
    (selected : Finset ι) (rank : α → Nat)
    (hdecrease : ∀ index ∈ selected, rank (target index) < rank (source index))
    (swaps : List (ι × ι))
    (hprod : (swaps.map (fun pair => Equiv.swap pair.1 pair.2)).prod = perm) :
    selected.card ≤ swaps.length :=
  (value_rank_card_le_arbitrarySwapCount source target perm hcompatible selected rank
    hdecrease).trans
    (Shuffler.Permute.Permutation.arbitrarySwapCount_le_length_swaps perm swaps hprod)

end Shuffler.Optimality.BirthPlacement
