import Shuffler.Optimality.BirthPlacement.Word
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Shuffler.Optimality.BirthPlacement.Word

variable {α : Type*} [DecidableEq α] {size reach : Nat}
variable {births target : Fin size → α}

theorem optimal_compatible (hcount : Balanced births target) (index : Fin size) :
    births index = target (optimal reach births target hcount index) :=
  (Equiv.ofFiberEquiv_map _ index).symm

theorem optimal_deadline (hcount : Balanced births target) (hbase : Feasible reach births target)
    (index : Fin size) : index.val ≤ (optimal reach births target hcount index).val + reach :=
  Endpoint.optimal_deadline (hcount (births index)) (hbase (births index))
    ((fiber births (births index)) ⟨index, rfl⟩)

theorem localMatching_deadline (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index))
    (hd : ∀ index, index.val ≤ (matching index).val + reach) (value : α)
    (position : positions births value) :
    position.val ≤ (localMatching births target matching hcompatible value position).val + reach :=
  hd ((fiber births value).symm position).val

theorem balanced_of_matching (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index)) : Balanced births target := by
  intro value
  have he := Fintype.card_congr (localMatching births target matching hcompatible value)
  simpa only [Fintype.card_coe] using he

theorem feasible_of_matching (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index))
    (hd : ∀ index, index.val ≤ (matching index).val + reach) : Feasible reach births target := by
  intro value
  exact Hall.condition_of_matching (localMatching births target matching hcompatible value)
    (localMatching_deadline matching hcompatible hd value)

theorem localMatching_fixed (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index)) (value : α) :
    Endpoint.fixed (localMatching births target matching hcompatible value) =
      ((fixed matching).filter fun index => births index = value).image Fin.val := by
  ext position
  constructor
  · intro hp
    obtain ⟨hb, he⟩ := (Endpoint.mem_fixed _ position).mp hp
    let index := (fiber births value).symm ⟨position, hb⟩
    have hfix : matching index.val = index.val := Fin.ext he
    exact Finset.mem_image.mpr ⟨index.val,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix⟩,
        index.property⟩, rfl⟩
  · intro hp
    obtain ⟨index, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hf, hv⟩ := Finset.mem_filter.mp hi
    have hfix := (Finset.mem_filter.mp hf).2
    have hb : index.val ∈ positions births value :=
      (mem_positions births value _).mpr ⟨index.isLt, hv⟩
    apply (Endpoint.mem_fixed _ _).mpr
    exact ⟨hb, congrArg Fin.val hfix⟩

theorem localMatching_optimal (hcount : Balanced births target) (value : α) :
    localMatching births target (optimal reach births target hcount) (optimal_compatible hcount) value =
      Endpoint.optimal reach (positions births value) (positions target value) (hcount value) := by
  apply Equiv.ext
  intro position
  rcases position with ⟨position, hposition⟩
  obtain ⟨hlt, he⟩ := (mem_positions births value position).mp hposition
  subst value
  apply Subtype.ext
  rfl

theorem local_fixed_card_le (hcount : Balanced births target)
    (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index))
    (hd : ∀ index, index.val ≤ (matching index).val + reach) (value : α) :
    ((fixed matching).filter fun index => births index = value).card ≤
      ((fixed (optimal reach births target hcount)).filter fun index => births index = value).card := by
  have hh := Endpoint.fixed_card_le (hcount value)
    (localMatching births target matching hcompatible value)
    (localMatching_deadline matching hcompatible hd value)
  rw [← localMatching_optimal hcount value,
    localMatching_fixed, localMatching_fixed] at hh
  simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hh

theorem fixed_card_le (hcount : Balanced births target)
    (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index))
    (hd : ∀ index, index.val ≤ (matching index).val + reach) :
    (fixed matching).card ≤ (fixed (optimal reach births target hcount)).card := by
  let values := Finset.univ.image births
  have hc (perm : Equiv.Perm (Fin size)) :
      (fixed perm).card = ∑ value ∈ values, ((fixed perm).filter fun index => births index = value).card :=
    Finset.card_eq_sum_card_fiberwise (fun index _ => Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
  rw [hc matching, hc (optimal reach births target hcount)]
  exact Finset.sum_le_sum (fun value _ => local_fixed_card_le hcount matching hcompatible hd value)

theorem fixed_add_support (matching : Equiv.Perm (Fin size)) :
    (fixed matching).card + matching.support.card = size := by
  simpa only [fixed, Equiv.Perm.support, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun index => matching index = index))

theorem support_card_le (hcount : Balanced births target)
    (matching : Equiv.Perm (Fin size))
    (hcompatible : ∀ index, births index = target (matching index))
    (hd : ∀ index, index.val ≤ (matching index).val + reach) :
    (optimal reach births target hcount).support.card ≤ matching.support.card := by
  have hc := fixed_card_le hcount matching hcompatible hd
  have ho := fixed_add_support (optimal reach births target hcount)
  have hm := fixed_add_support matching
  omega

end Shuffler.Optimality.BirthPlacement.Word
