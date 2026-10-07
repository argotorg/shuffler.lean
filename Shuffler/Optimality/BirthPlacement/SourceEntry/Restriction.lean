import Shuffler.Optimality.BirthPlacement.SourcePrefix.Cost
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace Shuffler.Optimality.BirthPlacement.SourceEntry

open Shuffler.Permute.Permutation

variable {size height : Nat}

def lowerEquiv (hh : height ≤ size) :
    Fin height ≃ {index : Fin size // index.val < height} where
  toFun index := ⟨Fin.castLE hh index, index.isLt⟩
  invFun index := ⟨index.val.val, index.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem maps_lower (permutation : Equiv.Perm (Fin size))
    (hfixed : ∀ index, height ≤ index.val → permutation index = index)
    (index : Fin size) (hi : index.val < height) : (permutation index).val < height := by
  by_contra hout
  have he := hfixed (permutation index) (by omega)
  have hi' := permutation.injective he
  have := congrArg Fin.val hi'
  omega

def restrict (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) :
    Equiv.Perm (Fin height) where
  toFun index := ⟨(permutation (Fin.castLE hh index)).val,
    maps_lower permutation hfixed _ index.isLt⟩
  invFun index := ⟨(permutation.symm (Fin.castLE hh index)).val, by
    by_contra hout
    have he := hfixed (permutation.symm (Fin.castLE hh index)) (by omega)
    rw [Equiv.apply_symm_apply] at he
    have := congrArg Fin.val he
    have := index.isLt
    simp only [Fin.val_castLE] at *
    omega⟩
  left_inv index := by
    apply Fin.ext
    exact congrArg (fun i : Fin size => i.val) (permutation.symm_apply_apply (Fin.castLE hh index))
  right_inv index := by
    apply Fin.ext
    exact congrArg (fun i : Fin size => i.val) (permutation.apply_symm_apply (Fin.castLE hh index))

@[simp] theorem restrict_apply (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) (index : Fin height) :
    Fin.castLE hh (restrict permutation hh hfixed index) = permutation (Fin.castLE hh index) := rfl

@[simp] theorem restrict_symm_apply (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) (index : Fin height) :
    Fin.castLE hh ((restrict permutation hh hfixed).symm index) =
      permutation.symm (Fin.castLE hh index) := rfl

theorem restrict_extendDomain (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) :
    (restrict permutation hh hfixed).extendDomain (lowerEquiv hh) = permutation := by
  apply Equiv.ext
  intro index
  by_cases hi : index.val < height
  · rw [Equiv.Perm.extendDomain_apply_subtype (restrict permutation hh hfixed) (lowerEquiv hh) hi]
    rfl
  · rw [Equiv.Perm.extendDomain_apply_not_subtype (restrict permutation hh hfixed) (lowerEquiv hh) hi]
    exact (hfixed index (by omega)).symm

theorem restrict_support_card (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) :
    (restrict permutation hh hfixed).support.card = permutation.support.card := by
  have he := Equiv.Perm.card_support_extend_domain (lowerEquiv hh)
    (g := restrict permutation hh hfixed)
  rw [restrict_extendDomain] at he
  exact he.symm

theorem restrict_cycleFactors_card (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) :
    (restrict permutation hh hfixed).cycleFactorsFinset.card =
      permutation.cycleFactorsFinset.card := by
  have he := Equiv.Perm.cycleType_extendDomain (lowerEquiv hh)
    (g := restrict permutation hh hfixed)
  rw [restrict_extendDomain] at he
  simpa only [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card] using
    (congrArg Multiset.card he).symm

theorem restrict_arbitrarySwapCount (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) :
    arbitrarySwapCount (restrict permutation hh hfixed) = arbitrarySwapCount permutation := by
  simp only [arbitrarySwapCount, restrict_support_card, restrict_cycleFactors_card]

theorem restrict_swapCount (permutation : Equiv.Perm (Fin size)) (hh : height ≤ size)
    (hfixed : ∀ index, height ≤ index.val → permutation index = index) (top : Fin height) :
    swapCount (restrict permutation hh hfixed) top = swapCount permutation (Fin.castLE hh top) := by
  have he : restrict permutation hh hfixed top = top ↔
      permutation (Fin.castLE hh top) = Fin.castLE hh top := by
    constructor
    · intro he
      simpa only [restrict_apply] using congrArg (Fin.castLE hh) he
    · intro he
      apply Fin.ext
      exact congrArg (fun i : Fin size => i.val) he
  simp only [swapCount_eq, restrict_support_card, restrict_cycleFactors_card, he]

end Shuffler.Optimality.BirthPlacement.SourceEntry
