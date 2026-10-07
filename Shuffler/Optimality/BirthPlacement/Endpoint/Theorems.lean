import Shuffler.Optimality.BirthPlacement.Endpoint

namespace Shuffler.Optimality.BirthPlacement.Endpoint

variable {births outputs selected : Finset Nat} {reach : Nat}

theorem extend_fixed (hb : selected ⊆ births) (ht : selected ⊆ outputs)
    (matching : ↥(births \ selected) ≃ ↥(outputs \ selected))
    (position : births) (hp : position.val ∈ selected) :
    (extend hb ht matching position).val = position.val := by
  simp [extend, extendMap, hp]

theorem extend_deadline (hb : selected ⊆ births) (ht : selected ⊆ outputs)
    (matching : ↥(births \ selected) ≃ ↥(outputs \ selected))
    (hd : ∀ position : ↥(births \ selected), position.val ≤ (matching position).val + reach)
    (position : births) : position.val ≤ (extend hb ht matching position).val + reach := by
  by_cases hp : position.val ∈ selected
  · rw [extend_fixed hb ht matching position hp]
    omega
  · simpa only [extend, Equiv.coe_fn_mk, extendMap, hp, dite_false] using
      hd ⟨position.val, Finset.mem_sdiff.mpr ⟨position.property, hp⟩⟩

theorem optimal_deadline (hcard : births.card = outputs.card)
    (hbase : Hall.Condition reach births outputs) (position : births) :
    position.val ≤ (optimal reach births outputs hcard position).val + reach := by
  apply extend_deadline
  intro reduced
  exact Hall.ordered_deadline
    (remaining_card hcard
      (fun _ h => (Finset.mem_inter.mp (Hall.fixed_subset _ _ _ h)).1)
      (fun _ h => (Finset.mem_inter.mp (Hall.fixed_subset _ _ _ h)).2))
    (Hall.fixed_remaining hbase) reduced

theorem mem_fixed (matching : births ≃ outputs) (position : Nat) :
    position ∈ fixed matching ↔
      ∃ hp : position ∈ births, (matching ⟨position, hp⟩).val = position := by
  constructor
  · intro hp
    obtain ⟨index, hi, he⟩ := Finset.mem_image.mp hp
    obtain ⟨_, hf⟩ := Finset.mem_filter.mp hi
    subst position
    exact ⟨index.property, hf⟩
  · rintro ⟨hp, he⟩
    exact Finset.mem_image.mpr ⟨⟨position, hp⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, he⟩, rfl⟩

theorem fixed_subset (matching : births ≃ outputs) : fixed matching ⊆ births ∩ outputs := by
  intro position hp
  obtain ⟨hb, he⟩ := (mem_fixed matching position).mp hp
  exact Finset.mem_inter.mpr ⟨hb, he ▸ (matching ⟨position, hb⟩).property⟩

theorem chosen_subset_fixed (hcard : births.card = outputs.card) :
    Hall.fixed reach births outputs ⊆ fixed (optimal reach births outputs hcard) := by
  intro position hp
  have hb := (Finset.mem_inter.mp (Hall.fixed_subset reach births outputs hp)).1
  apply (mem_fixed _ _).mpr
  exact ⟨hb, extend_fixed _ _ _ ⟨position, hb⟩ hp⟩

theorem matching_mem_fixed_iff (matching : births ≃ outputs) (position : births) :
    (matching position).val ∈ fixed matching ↔ position.val ∈ fixed matching := by
  constructor
  · intro hp
    obtain ⟨hb, he⟩ := (mem_fixed matching _).mp hp
    have heq : matching ⟨(matching position).val, hb⟩ = matching position := Subtype.ext he
    have hb' := congrArg (fun index : births => index.val) (matching.injective heq)
    exact (mem_fixed matching _).mpr ⟨position.property, hb'⟩
  · intro hp
    obtain ⟨_, he⟩ := (mem_fixed matching _).mp hp
    simpa only [he] using hp

def removeFixed (matching : births ≃ outputs) :
    ↥(births \ fixed matching) ≃ ↥(outputs \ fixed matching) where
  toFun position :=
    let birth : births := ⟨position.val, (Finset.mem_sdiff.mp position.property).1⟩
    ⟨(matching birth).val, Finset.mem_sdiff.mpr ⟨(matching birth).property,
      fun hm => (Finset.mem_sdiff.mp position.property).2
        ((matching_mem_fixed_iff matching birth).mp hm)⟩⟩
  invFun position :=
    let output : outputs := ⟨position.val, (Finset.mem_sdiff.mp position.property).1⟩
    let birth := matching.symm output
    ⟨birth.val, Finset.mem_sdiff.mpr ⟨birth.property,
      fun hm => (Finset.mem_sdiff.mp position.property).2 (by
        have ht := (matching_mem_fixed_iff matching birth).mpr hm
        simpa only [birth, Equiv.apply_symm_apply] using ht)⟩⟩
  left_inv position := by
    apply Subtype.ext
    exact congrArg (fun index : births => index.val)
      (matching.symm_apply_apply ⟨position.val, (Finset.mem_sdiff.mp position.property).1⟩)
  right_inv position := by
    apply Subtype.ext
    exact congrArg (fun index : outputs => index.val)
      (matching.apply_symm_apply ⟨position.val, (Finset.mem_sdiff.mp position.property).1⟩)

theorem fixed_remaining (matching : births ≃ outputs)
    (hd : ∀ position : births, position.val ≤ (matching position).val + reach) :
    Hall.Condition reach (births \ fixed matching) (outputs \ fixed matching) := by
  apply Hall.condition_of_matching (removeFixed matching)
  intro position
  exact hd ⟨position.val, (Finset.mem_sdiff.mp position.property).1⟩

theorem fixed_card_le (hcard : births.card = outputs.card)
    (matching : births ≃ outputs)
    (hd : ∀ position : births, position.val ≤ (matching position).val + reach) :
    (fixed matching).card ≤ (fixed (optimal reach births outputs hcard)).card := by
  have hbase := Hall.condition_of_matching matching hd
  exact (Hall.fixed_optimal hbase (fixed_subset matching) (fixed_remaining matching hd)).trans
    (Finset.card_le_card (chosen_subset_fixed hcard))

theorem optimal_fixed_eq (hcard : births.card = outputs.card)
    (hbase : Hall.Condition reach births outputs) :
    fixed (optimal reach births outputs hcard) = Hall.fixed reach births outputs := by
  symm
  apply Finset.eq_of_subset_of_card_le (chosen_subset_fixed hcard)
  exact Hall.fixed_optimal hbase (fixed_subset _) (fixed_remaining _ (optimal_deadline hcard hbase))

end Shuffler.Optimality.BirthPlacement.Endpoint
