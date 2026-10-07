import Shuffler.Optimality.Collective.Deadlines
import Mathlib.Data.Multiset.AddSub

namespace Shuffler.Optimality.Collective

theorem deadlineOrigin_lt_iff (selected : Finset (Interval target)) (index : Fin target.length)
    (cut : Nat) :
    deadlineOrigin selected index < cut ↔ index.val < cut ∨
      ∃ gap ∈ selected, gap.stop = index ∧ gap.start.val < cut := by
  let positions := insert index.val
    ((selected.filter fun gap => gap.stop = index).image fun gap => gap.start.val)
  have hn : positions.Nonempty := ⟨index.val, Finset.mem_insert_self _ _⟩
  have hc : positions.min' hn < cut ↔ ∃ position ∈ positions, position < cut := by
    constructor
    · intro hlt
      exact ⟨positions.min' hn, Finset.min'_mem positions hn, hlt⟩
    · rintro ⟨position, hmem, hlt⟩
      exact (Finset.min'_le positions position hmem).trans_lt hlt
  change positions.min' hn < cut ↔ _
  rw [hc]
  simp only [positions, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨position, hp, hlt⟩
    rcases hp with rfl | ⟨gap, ⟨hmem, hstop⟩, rfl⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨gap, hmem, hstop, hlt⟩
  · rintro (hlt | ⟨gap, hmem, hstop, hlt⟩)
    · exact ⟨index.val, Or.inl rfl, hlt⟩
    · exact ⟨gap.start.val, Or.inr ⟨gap, ⟨hmem, hstop⟩, rfl⟩, hlt⟩

private theorem newPositions_cons_present (source target : Stack) (value : Value)
    (hmem : value ∈ source) :
    (newPositions source (value :: target)).card =
      (newPositions (source.erase value) target).card := by
  have hpositive : 0 < source.count value := List.count_pos_iff.mpr hmem
  unfold newPositions
  simp only [List.length_cons]
  rw [Fin.card_filter_univ_succ' (fun index : Fin (target.length + 1) =>
    source.count (value :: target)[index] ≤
      (value :: target).countBefore (value :: target)[index] index.val)]
  simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, List.countBefore_zero,
    Nat.le_zero, Nat.ne_of_gt hpositive, ↓reduceIte, Nat.zero_add]
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_succ, List.getElem_cons_succ, List.countBefore_cons_succ]
  by_cases he : target[index.val] = value
  · rw [he]
    simp only [beq_self_eq_true, ↓reduceIte, List.count_erase_self]
    omega
  · simp [List.count_erase_of_ne he, Ne.symm he]

private theorem newPositions_cons_absent (source target : Stack) (value : Value)
    (hmem : value ∉ source) :
    (newPositions source (value :: target)).card =
      1 + (newPositions source target).card := by
  have hzero : source.count value = 0 := List.count_eq_zero.mpr hmem
  unfold newPositions
  simp only [List.length_cons]
  rw [Fin.card_filter_univ_succ' (fun index : Fin (target.length + 1) =>
    source.count (value :: target)[index] ≤
      (value :: target).countBefore (value :: target)[index] index.val)]
  simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, List.countBefore_zero,
    hzero, le_refl, ↓reduceIte]
  congr 2
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_succ, List.getElem_cons_succ, List.countBefore_cons_succ]
  by_cases he : target[index.val] = value
  · simp [he, hzero]
  · simp [Ne.symm he]

theorem newPositions_card (source target : Stack) :
    (newPositions source target).card =
      ((target : Multiset Value) - (source : Multiset Value)).card := by
  induction target generalizing source with
  | nil => simp [newPositions, Multiset.zero_sub]
  | cons value target ih =>
    by_cases hmem : value ∈ source
    · rw [newPositions_cons_present source target value hmem, ih]
      congr 1
      apply Multiset.ext.mpr
      intro other
      simp only [Multiset.count_sub, Multiset.coe_count]
      by_cases he : other = value
      · subst other
        have hp : 0 < source.count value := List.count_pos_iff.mpr hmem
        simp only [List.count_erase_self, List.count_cons_self]
        omega
      · simp [List.count_erase_of_ne he, Ne.symm he]
    · rw [newPositions_cons_absent source target value hmem, ih]
      have he : ((value :: target : Stack) : Multiset Value) - (source : Multiset Value) =
          value ::ₘ ((target : Multiset Value) - (source : Multiset Value)) := by
        apply Multiset.ext.mpr
        intro other
        simp only [Multiset.count_sub, Multiset.coe_count, Multiset.count_cons]
        by_cases he : other = value
        · subst other
          simp [List.count_eq_zero.mpr hmem]
        · simp [he, Ne.symm he]
      rw [he, Multiset.card_cons]
      omega

theorem newPositions_card_add_source (source target : Stack) :
    (newPositions source target).card + source.length =
      target.length + ((source : Multiset Value) - (target : Multiset Value)).card := by
  have hbalance : (target : Multiset Value) - (source : Multiset Value) +
      (source : Multiset Value) =
      (target : Multiset Value) + ((source : Multiset Value) - (target : Multiset Value)) := by
    apply Multiset.ext.mpr
    intro value
    simp only [Multiset.count_add, Multiset.count_sub]
    omega
  have hc := congrArg Multiset.card hbalance
  simpa only [Multiset.card_add, Multiset.coe_card, ← newPositions_card] using hc

-- At a cut, old copies already used plus old copies still required add to
-- the source length. The other outputs are new-copy jobs.
theorem newPositions_take_card_balance (source target : Stack) (cut : Nat)
    (hcut : cut ≤ target.length) :
    (newPositions source (target.take cut)).card + source.length =
      cut + (mandatory source target cut).card := by
  simpa only [List.length_take, Nat.min_eq_left hcut, mandatory] using
    newPositions_card_add_source source (target.take cut)

theorem newBefore_card (source target : Stack) (cut : Nat) :
    (newBefore source target cut).card = (newPositions source (target.take cut)).card := by
  symm
  apply Finset.card_bij (fun index _ =>
    (⟨index.val, by have := index.isLt; simp only [List.length_take] at this; omega⟩ :
      Fin target.length))
  · intro index hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hb : index.val < cut := by
      have := index.isLt
      simp only [List.length_take] at this
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hb⟩
    simpa only [Fin.getElem_fin, List.getElem_take, List.countBefore_eq_count_take,
      List.take_take, Nat.min_eq_left (Nat.le_of_lt hb)] using hi'
  · intro left _ right _ he
    exact Fin.ext (congrArg (fun index : Fin target.length => index.val) he)
  · intro index hi
    have hb := (Finset.mem_filter.mp hi).2
    let before : Fin (target.take cut).length :=
      ⟨index.val, by simp only [List.length_take]; omega⟩
    refine ⟨before, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    simpa only [before, Fin.getElem_fin, List.getElem_take, List.countBefore_eq_count_take,
      List.take_take, Nat.min_eq_left (Nat.le_of_lt hb)] using hn

theorem newBefore_card_balance (source target : Stack) (cut : Nat)
    (hcut : cut ≤ target.length) :
    (newBefore source target cut).card + source.length =
      cut + (mandatory source target cut).card := by
  rw [newBefore_card]
  exact newPositions_take_card_balance source target cut hcut

theorem Interval.stop_injective : Function.Injective (Interval.stop (fresh := target)) := by
  intro left right he
  apply Interval.eq_of_crosses_of_value_eq left right left.stop.val
  · exact ⟨left.property.1, Nat.le_refl _⟩
  · exact ⟨by rw [he]; exact right.property.1, by rw [he]⟩
  · change target[left.start] = target[right.start]
    exact left.property.2.1.trans ((congrArg (fun index => target[index]) he).trans
      right.property.2.1.symm)

theorem Interval.Paid.stop_mem_newPositions (gap : Interval target)
    (hpaid : gap.Paid source) : gap.stop ∈ newPositions source target := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [List.countBefore_eq_count_take]
  have hcount : (target.take (gap.start.val + 1)).count gap.value ≤
      (target.take gap.stop.val).count gap.value :=
    (List.take_sublist_take_left (Nat.succ_le_of_lt gap.property.1)).count_le _
  have he : target[gap.stop] = gap.value := gap.property.2.1.symm
  rw [he]
  exact hpaid.trans hcount

theorem dueBefore_eq_union (source target : Stack) (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source) (cut : Nat) :
    dueBefore source target selected cut = newBefore source target cut ∪
      (selected.filter fun gap => gap.Crosses cut).image Interval.stop := by
  ext index
  simp only [dueBefore, newBefore, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image, deadlineOrigin_lt_iff]
  constructor
  · rintro ⟨hnew, hown | ⟨gap, hmem, he, hstart⟩⟩
    · exact Or.inl ⟨hnew, hown⟩
    · by_cases hbefore : index.val < cut
      · exact Or.inl ⟨hnew, hbefore⟩
      · exact Or.inr ⟨gap, ⟨hmem, hstart, by rw [he]; omega⟩, he⟩
  · rintro (⟨hnew, hown⟩ | ⟨gap, ⟨hmem, hcross⟩, he⟩)
    · exact ⟨hnew, Or.inl hown⟩
    · refine ⟨he ▸ Interval.Paid.stop_mem_newPositions gap (hpaid gap hmem), ?_⟩
      exact Or.inr ⟨gap, hmem, he, hcross.1⟩

theorem dueBefore_card (source target : Stack) (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source) (cut : Nat) :
    (dueBefore source target selected cut).card = (newBefore source target cut).card +
      (selected.filter fun gap => gap.Crosses cut).card := by
  have hd : Disjoint (newBefore source target cut)
      ((selected.filter fun gap => gap.Crosses cut).image Interval.stop) := by
    apply Finset.disjoint_left.mpr
    intro index hbefore hcross
    have hb := (Finset.mem_filter.mp hbefore).2
    obtain ⟨gap, hg, he⟩ := Finset.mem_image.mp hcross
    have hs := (Finset.mem_filter.mp hg).2.2
    rw [he] at hs
    omega
  rw [dueBefore_eq_union source target selected hpaid cut,
    Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Interval.stop_injective]

-- At each cut, the jobs due are exactly the new outputs before the cut
-- plus one job for each retained interval across it.
theorem dueBefore_card_balance (source target : Stack) (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source) (cut : Nat) (hcut : cut ≤ target.length) :
    (dueBefore source target selected cut).card + source.length =
      cut + (mandatory source target cut).card +
        (selected.filter fun gap => gap.Crosses cut).card := by
  rw [dueBefore_card source target selected hpaid cut]
  have hb := newBefore_card_balance source target cut hcut
  omega

theorem mem_dueBefore_iff_deadline (source target : Stack)
    (selected : Finset (Interval target)) (cut reach : Nat) (index : Fin target.length) :
    index ∈ dueBefore source target selected cut ↔ index ∈ newPositions source target ∧
      birthDeadline reach source.length selected index ≤ (cut : Int) + reach - source.length := by
  simp only [dueBefore, Finset.mem_filter, birthDeadline]
  constructor
  · rintro ⟨hnew, hlt⟩
    exact ⟨hnew, by omega⟩
  · rintro ⟨hnew, hle⟩
    exact ⟨hnew, by omega⟩

-- Signed arithmetic preserves the impossible deadline at source size
-- reach+1. Nat subtraction would turn that negative capacity into zero.
theorem deadline_capacity_iff (source target : Stack) (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source) (cut reach : Nat)
    (hcut : cut ≤ target.length) :
    ((dueBefore source target selected cut).card : Int) ≤
        (cut : Int) + reach - source.length ↔
      (mandatory source target cut).card +
        (selected.filter fun gap => gap.Crosses cut).card ≤ reach := by
  have hb := dueBefore_card_balance source target selected hpaid cut hcut
  omega

end Shuffler.Optimality.Collective
