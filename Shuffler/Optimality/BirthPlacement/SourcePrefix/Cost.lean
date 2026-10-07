import Shuffler.Optimality.BirthPlacement.SourcePrefix.Theorems
import Shuffler.Permute.Optimality

namespace Shuffler.Permute.Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem arbitrarySwapCount_mul_le (first second : Equiv.Perm ι) :
    arbitrarySwapCount (first * second) ≤ arbitrarySwapCount first + arbitrarySwapCount second := by
  obtain ⟨firstSwaps, hf, hfc⟩ := exists_swaps first
  obtain ⟨secondSwaps, hs, hsc⟩ := exists_swaps second
  have h := arbitrarySwapCount_le_length_swaps (first * second) (firstSwaps ++ secondSwaps)
    (by simp only [List.map_append, List.prod_append, hf, hs])
  simpa only [List.length_append, hfc, hsc] using h

@[simp] theorem arbitrarySwapCount_inv (permutation : Equiv.Perm ι) :
    arbitrarySwapCount permutation⁻¹ = arbitrarySwapCount permutation := by
  have bound (permutation : Equiv.Perm ι) :
      arbitrarySwapCount permutation⁻¹ ≤ arbitrarySwapCount permutation := by
    obtain ⟨swaps, hp, hc⟩ := exists_swaps permutation
    have hprod : (swaps.reverse.map fun pair => Equiv.swap pair.1 pair.2).prod = permutation⁻¹ := by
      rw [← hp, List.prod_inv_reverse, List.map_reverse]
      simp only [List.map_map, Function.comp_def, Equiv.swap_inv]
    simpa only [List.length_reverse, hc] using
      arbitrarySwapCount_le_length_swaps permutation⁻¹ swaps.reverse hprod
  exact (bound permutation).antisymm (by simpa only [inv_inv] using bound permutation⁻¹)

@[simp] theorem cyclesAwayFromTop_inv_card (permutation : Equiv.Perm ι) (top : ι) :
    (cyclesAwayFromTop permutation⁻¹ top).card = (cyclesAwayFromTop permutation top).card := by
  have hf := arbitrarySwapCount_add_cyclesAwayFromTop permutation top
  have hi := arbitrarySwapCount_add_cyclesAwayFromTop permutation⁻¹ top
  rw [arbitrarySwapCount_inv, Equiv.Perm.support_inv] at hi
  omega

@[simp] theorem swapCount_inv (permutation : Equiv.Perm ι) (top : ι) :
    swapCount permutation⁻¹ top = swapCount permutation top := by
  simp only [swapCount_eq_arbitrarySwapCount_add, arbitrarySwapCount_inv, cyclesAwayFromTop_inv_card]

end Shuffler.Permute.Permutation

namespace Shuffler.Optimality.BirthPlacement.SourcePrefix

open Shuffler.Permute.Permutation

theorem permutation_cost (assignment : Equiv.Perm (Fin size)) (height : Nat) (hh : height ≤ size) :
    arbitrarySwapCount (permutation assignment height) = (run assignment height).swaps.length := by
  have upper := arbitrarySwapCount_le_length_swaps (permutation assignment height)
    (run assignment height).swaps rfl
  obtain ⟨_, _, hc, hp, _⟩ := run_spec assignment height hh
  have lower := arbitrarySwapCount_mul_le (run assignment height).permutation
    (permutation assignment height)⁻¹
  have he : (run assignment height).permutation * (permutation assignment height)⁻¹ = assignment := by
    rw [← hp, mul_assoc, mul_inv_cancel, mul_one]
  rw [he, arbitrarySwapCount_inv] at lower
  omega

theorem permutation_cost_add_remaining (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) :
    arbitrarySwapCount (permutation assignment height) +
      arbitrarySwapCount (run assignment height).permutation = arbitrarySwapCount assignment := by
  rw [permutation_cost assignment height hh]
  have hc := (run_spec assignment height hh).2.2.1
  omega

theorem entry_cost_add_remaining (assignment : Equiv.Perm (Fin size)) (height : Nat)
    (hh : height ≤ size) (top : Fin size) :
    swapCount (permutation assignment height)⁻¹ top +
      arbitrarySwapCount (run assignment height).permutation =
        arbitrarySwapCount assignment +
          2 * (cyclesAwayFromTop (permutation assignment height) top).card := by
  rw [swapCount_inv, swapCount_eq_arbitrarySwapCount_add]
  have hc := permutation_cost_add_remaining assignment height hh
  omega

end Shuffler.Optimality.BirthPlacement.SourcePrefix
