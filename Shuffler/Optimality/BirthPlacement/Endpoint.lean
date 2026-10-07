import Shuffler.Optimality.BirthPlacement.Hall.Theorems

namespace Shuffler.Optimality.BirthPlacement.Endpoint

variable {births outputs selected : Finset Nat}

def extendMap (hsub : selected ⊆ outputs)
    (matching : ↥(births \ selected) → ↥(outputs \ selected)) (position : births) : outputs :=
  if h : position.val ∈ selected then ⟨position.val, hsub h⟩
  else
    let next := matching ⟨position.val, Finset.mem_sdiff.mpr ⟨position.property, h⟩⟩
    ⟨next.val, (Finset.mem_sdiff.mp next.property).1⟩

theorem extendMap_inverse (hb : selected ⊆ births) (ht : selected ⊆ outputs)
    (matching : ↥(births \ selected) ≃ ↥(outputs \ selected)) (position : births) :
    extendMap hb matching.symm (extendMap ht matching position) = position := by
  by_cases hp : position.val ∈ selected
  · apply Subtype.ext
    simp [extendMap, hp]
  · let reduced : ↥(births \ selected) :=
      ⟨position.val, Finset.mem_sdiff.mpr ⟨position.property, hp⟩⟩
    have hn : (matching reduced).val ∉ selected :=
      (Finset.mem_sdiff.mp (matching reduced).property).2
    apply Subtype.ext
    rw [show extendMap ht matching position =
      ⟨(matching reduced).val, (Finset.mem_sdiff.mp (matching reduced).property).1⟩ by
        simp only [extendMap, hp, dite_false]; rfl]
    simp only [extendMap, hn, dite_false]
    change (matching.symm (matching reduced)).val = position.val
    simp [reduced]

def extend (hb : selected ⊆ births) (ht : selected ⊆ outputs)
    (matching : ↥(births \ selected) ≃ ↥(outputs \ selected)) : births ≃ outputs where
  toFun := extendMap ht matching
  invFun := extendMap hb matching.symm
  left_inv := extendMap_inverse hb ht matching
  right_inv := extendMap_inverse ht hb matching.symm

theorem remaining_card (hcard : births.card = outputs.card)
    (hb : selected ⊆ births) (ht : selected ⊆ outputs) :
    (births \ selected).card = (outputs \ selected).card := by
  rw [Finset.card_sdiff_of_subset hb, Finset.card_sdiff_of_subset ht, hcard]

def optimal (reach : Nat) (births outputs : Finset Nat)
    (hcard : births.card = outputs.card) : births ≃ outputs :=
  let chosen := Hall.fixed reach births outputs
  have hb : chosen ⊆ births := fun _ h => (Finset.mem_inter.mp (Hall.fixed_subset _ _ _ h)).1
  have ht : chosen ⊆ outputs := fun _ h => (Finset.mem_inter.mp (Hall.fixed_subset _ _ _ h)).2
  extend hb ht (Hall.ordered (births \ chosen) (outputs \ chosen) (remaining_card hcard hb ht)).toEquiv

def fixed (matching : births ≃ outputs) : Finset Nat :=
  births.attach.filter (fun position => (matching position).val = position.val) |>.image Subtype.val

end Shuffler.Optimality.BirthPlacement.Endpoint
