import Shuffler.Optimality.BirthPlacement.Endpoint.Theorems
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Shuffler.Optimality.BirthPlacement.Word

variable {α : Type*} [DecidableEq α] {size : Nat}

def positions (word : Fin size → α) (value : α) : Finset Nat :=
  (Finset.univ.filter fun index => word index = value).image Fin.val

theorem mem_positions (word : Fin size → α) (value : α) (position : Nat) :
    position ∈ positions word value ↔
      ∃ hp : position < size, word ⟨position, hp⟩ = value := by
  constructor
  · intro hp
    obtain ⟨index, hi, he⟩ := Finset.mem_image.mp hp
    subst position
    exact ⟨index.isLt, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨hp, he⟩
    exact Finset.mem_image.mpr ⟨⟨position, hp⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

def fiber (word : Fin size → α) (value : α) :
    {index // word index = value} ≃ positions word value where
  toFun index := ⟨index.val.val, (mem_positions word value _).mpr ⟨index.val.isLt, index.property⟩⟩
  invFun position :=
    let hp := (mem_positions word value position.val).mp position.property
    have hlt : position.val < size := by obtain ⟨hlt, _⟩ := hp; exact hlt
    have he : word ⟨position.val, hlt⟩ = value := by obtain ⟨_, he⟩ := hp; exact he
    ⟨⟨position.val, hlt⟩, he⟩
  left_inv index := by rfl
  right_inv index := by rfl

def Balanced (births target : Fin size → α) : Prop :=
  ∀ value, (positions births value).card = (positions target value).card

def Feasible (reach : Nat) (births target : Fin size → α) : Prop :=
  ∀ value, Hall.Condition reach (positions births value) (positions target value)

def optimal (reach : Nat) (births target : Fin size → α) (hcount : Balanced births target) :
    Equiv.Perm (Fin size) :=
  Equiv.ofFiberEquiv fun value => (fiber births value).trans
    ((Endpoint.optimal reach (positions births value) (positions target value) (hcount value)).trans
      (fiber target value).symm)

def localMatching (births target : Fin size → α) (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index)) (value : α) :
    positions births value ≃ positions target value :=
  (fiber births value).symm.trans
    ((matching.subtypeEquiv (fun index => by rw [hcompatible index])).trans (fiber target value))

def fixed (matching : Equiv.Perm (Fin size)) : Finset (Fin size) :=
  Finset.univ.filter fun index => matching index = index

end Shuffler.Optimality.BirthPlacement.Word
