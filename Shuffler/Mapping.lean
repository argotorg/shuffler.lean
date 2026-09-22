import Shuffler.Defs
import Shuffler.Permute.Defs
import Mathlib.Data.Fintype.EquivFin

theorem Mapping.complete_of_target_total
    (mapping : Mapping source target)
    (hsize : source.length ≤ target.length)
    (htarget : ∀ j, (mapping.symm j).isSome) :
    source.length = target.length ∧ ∀ i, (mapping i).isSome := by
  let position := fun j => (mapping.symm j).get (htarget j)
  have hposition : ∀ j, mapping (position j) = some j := fun j =>
    mapping.eq_some_iff.mp (Option.some_get (htarget j)).symm
  have hinj : Function.Injective position := by
    intro j k h
    apply Option.some_injective
    rw [← hposition j, ← hposition k, h]
  have hlen : source.length = target.length :=
    Nat.le_antisymm hsize (by simpa using Fintype.card_le_of_injective position hinj)
  have hsurj : Function.Surjective position :=
    ((Fintype.bijective_iff_injective_and_card position).mpr
      ⟨hinj, by simp [hlen]⟩).2
  refine ⟨hlen, ?_⟩
  intro i
  obtain ⟨j, rfl⟩ := hsurj i
  rw [hposition j]
  rfl

-- Each current position goes to its assigned target position.
def Mapping.toPermutation
    (mapping : Mapping source target)
    (hsize : source.length ≤ target.length)
    (htarget : ∀ j, (mapping.symm j).isSome) : Shuffler.Permute.Permutation source :=
  have hcomplete := mapping.complete_of_target_total hsize htarget
  let equiv : Fin source.length ≃ Fin target.length := {
    toFun := fun i => (mapping i).get (hcomplete.2 i)
    invFun := fun j => (mapping.symm j).get (htarget j)
    left_inv := fun i => by
      apply Option.some_injective
      rw [Option.some_get]
      exact mapping.eq_some_iff.mpr (Option.some_get (hcomplete.2 i)).symm
    right_inv := fun j => by
      apply Option.some_injective
      rw [Option.some_get]
      exact mapping.eq_some_iff.mp (Option.some_get (htarget j)).symm
  }
  equiv.trans (finCongr hcomplete.1.symm)
