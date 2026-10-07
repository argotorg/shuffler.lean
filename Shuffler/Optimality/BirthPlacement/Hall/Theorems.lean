import Shuffler.Optimality.BirthPlacement.Hall
import Shuffler.Optimality.BirthPlacement.Reservations.Theorems

namespace Shuffler.Optimality.BirthPlacement.Hall

variable {births outputs selected positions : Finset Nat} {reach cut : Nat}

theorem born_partition (hsub : selected ⊆ positions) :
    (born (positions \ selected) cut).card + (born selected cut).card = (born positions cut).card := by
  have hs : born selected cut ⊆ born positions cut := Finset.filter_subset_filter _ hsub
  have he : born (positions \ selected) cut = born positions cut \ born selected cut := by
    ext position
    simp only [born, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card hs

theorem due_partition (hsub : selected ⊆ positions) :
    (due reach (positions \ selected) cut).card + (due reach selected cut).card =
      (due reach positions cut).card := by
  have hs : due reach selected cut ⊆ due reach positions cut := Finset.filter_subset_filter _ hsub
  have he : due reach (positions \ selected) cut = due reach positions cut \ due reach selected cut := by
    ext position
    simp only [due, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card hs

theorem born_eq_due_add_load (reach cut : Nat) (selected : Finset Nat) :
    (born selected cut).card = (due reach selected cut).card + Reservations.load reach selected cut := by
  have hs : due reach selected cut ⊆ born selected cut := by
    intro position hp
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hm, by omega⟩
  have he : born selected cut \ due reach selected cut =
      selected.filter (fun position => Reservations.Covers reach position cut) := by
    ext position
    constructor
    · intro hp
      obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hb
      apply Finset.mem_filter.mpr
      refine ⟨hm, hc, ?_⟩
      by_contra hl
      exact hn (Finset.mem_filter.mpr ⟨hm, by omega⟩)
    · intro hp
      obtain ⟨hm, hc, hl⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hm, hc⟩, ?_⟩
      intro hd
      have hd := (Finset.mem_filter.mp hd).2
      omega
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [he] at hc
  exact (Nat.add_comm _ _).trans hc |>.symm

theorem remaining_iff_reservations (hsub : selected ⊆ births ∩ outputs)
    (hbase : Condition reach births outputs) :
    Condition reach (births \ selected) (outputs \ selected) ↔
      Reservations.Feasible reach (slack reach births outputs) selected := by
  have hb : selected ⊆ births := fun position hp => (Finset.mem_inter.mp (hsub hp)).1
  have ht : selected ⊆ outputs := fun position hp => (Finset.mem_inter.mp (hsub hp)).2
  constructor
  · intro hr cut
    have hborn := born_partition (cut := cut) hb
    have hdue := due_partition (reach := reach) (cut := cut) ht
    have hload := born_eq_due_add_load reach cut selected
    have hremain := hr cut
    unfold slack
    omega
  · intro hf cut
    have hborn := born_partition (cut := cut) hb
    have hdue := due_partition (reach := reach) (cut := cut) ht
    have hload := born_eq_due_add_load reach cut selected
    have hremain := hf cut
    have htotal := hbase cut
    change Reservations.load reach selected cut ≤
      (born births cut).card - (due reach outputs cut).card at hremain
    omega

theorem fixed_subset (reach : Nat) (births outputs : Finset Nat) :
    fixed reach births outputs ⊆ births ∩ outputs := by
  simpa only [fixed, Finset.sort_toFinset] using Reservations.select_subset reach (slack reach births outputs)
    ((births ∩ outputs).sort (· ≤ ·))

theorem fixed_feasible (reach : Nat) (births outputs : Finset Nat) :
    Reservations.Feasible reach (slack reach births outputs) (fixed reach births outputs) :=
  Reservations.select_feasible _ _ _ (Finset.sort_nodup _ _)

theorem fixed_remaining (hbase : Condition reach births outputs) :
    Condition reach (births \ fixed reach births outputs) (outputs \ fixed reach births outputs) :=
  (remaining_iff_reservations (fixed_subset _ _ _) hbase).mpr (fixed_feasible _ _ _)

theorem fixed_optimal (hbase : Condition reach births outputs)
    (hsub : selected ⊆ births ∩ outputs)
    (hremain : Condition reach (births \ selected) (outputs \ selected)) :
    selected.card ≤ (fixed reach births outputs).card := by
  apply Reservations.select_optimal _ _ _ (Finset.sortedLT_sort _).pairwise selected
  · simpa only [Finset.sort_toFinset] using hsub
  · exact (remaining_iff_reservations hsub hbase).mp hremain

theorem condition_of_matching (matching : births ≃ outputs)
    (hdeadline : ∀ position : births, position.val ≤ (matching position).val + reach) :
    Condition reach births outputs := by
  intro cut
  let pending := due reach outputs cut
  let back : pending → Nat := fun position =>
    (matching.symm ⟨position.val, (Finset.mem_filter.mp position.property).1⟩).val
  have hinj : Function.Injective back := by
    intro left right he
    have hb : matching.symm ⟨left.val, (Finset.mem_filter.mp left.property).1⟩ =
        matching.symm ⟨right.val, (Finset.mem_filter.mp right.property).1⟩ := Subtype.ext he
    have ht := matching.symm.injective hb
    exact Subtype.ext (congrArg (fun index : outputs => index.val) ht)
  have hsub : pending.attach.image back ⊆ born births cut := by
    intro position hp
    obtain ⟨output, _, rfl⟩ := Finset.mem_image.mp hp
    let birth := matching.symm ⟨output.val, (Finset.mem_filter.mp output.property).1⟩
    have hd := hdeadline birth
    have hf : (matching birth).val = output.val := by simp [birth]
    have ht := (Finset.mem_filter.mp output.property).2
    refine Finset.mem_filter.mpr ⟨birth.property, ?_⟩
    change birth.val ≤ cut
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach] at hc
  exact hc

theorem ordered_deadline (hcard : births.card = outputs.card)
    (hbase : Condition reach births outputs) (position : births) :
    position.val ≤ (ordered births outputs hcard position).val + reach := by
  let output := ordered births outputs hcard position
  by_contra hn
  have hlate : output.val + reach < position.val := Nat.lt_of_not_ge hn
  let earlier := born births (output.val + reach)
  let forward : earlier → Nat := fun index =>
    (ordered births outputs hcard ⟨index.val, (Finset.mem_filter.mp index.property).1⟩).val
  have hinj : Function.Injective forward := by
    intro left right he
    have ht : ordered births outputs hcard ⟨left.val, (Finset.mem_filter.mp left.property).1⟩ =
        ordered births outputs hcard ⟨right.val, (Finset.mem_filter.mp right.property).1⟩ := Subtype.ext he
    have hb := (ordered births outputs hcard).injective ht
    exact Subtype.ext (congrArg (fun index : births => index.val) hb)
  have hsub : earlier.attach.image forward ⊆ (born outputs output.val).erase output.val := by
    intro index hi
    obtain ⟨birth, _, rfl⟩ := Finset.mem_image.mp hi
    have hb := (Finset.mem_filter.mp birth.property).2
    have hlt : (⟨birth.val, (Finset.mem_filter.mp birth.property).1⟩ : births) < position := by
      change birth.val < position.val
      omega
    have ho := (ordered births outputs hcard).strictMono hlt
    change forward birth < output.val at ho
    exact Finset.mem_erase.mpr ⟨Nat.ne_of_lt ho,
      Finset.mem_filter.mpr ⟨(ordered births outputs hcard _).property, Nat.le_of_lt ho⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach] at hc
  have hout : output.val ∈ born outputs output.val :=
    Finset.mem_filter.mpr ⟨output.property, Nat.le_refl _⟩
  have hcount := Finset.card_erase_add_one hout
  have hhall := hbase (output.val + reach)
  have he : due reach outputs (output.val + reach) = born outputs output.val := by
    ext index
    simp only [due, born, Finset.mem_filter]
    constructor <;> rintro ⟨hm, hi⟩ <;> exact ⟨hm, by omega⟩
  rw [he] at hhall
  change (born outputs output.val).card ≤ earlier.card at hhall
  omega

theorem condition_iff_ordered_deadline (hcard : births.card = outputs.card) :
    Condition reach births outputs ↔
      ∀ position : births, position.val ≤ (ordered births outputs hcard position).val + reach :=
  ⟨fun hbase => ordered_deadline hcard hbase,
    fun hdeadline => condition_of_matching (ordered births outputs hcard).toEquiv hdeadline⟩

end Shuffler.Optimality.BirthPlacement.Hall
