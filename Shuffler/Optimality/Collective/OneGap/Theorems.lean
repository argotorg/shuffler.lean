import Shuffler.Optimality.Collective.OneGap

namespace Shuffler.Optimality.Collective.OneGap

theorem firstOccurrence_value [DecidableEq α] (values : Fin size → α) (index : Fin size) :
    values (firstOccurrence values index) = values index := by
  have hm := Finset.min'_mem (Finset.univ.filter fun other => values other = values index)
    ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (Finset.mem_filter.mp hm).2

theorem firstOccurrence_le [DecidableEq α] (values : Fin size → α) (index : Fin size) :
    firstOccurrence values index ≤ index :=
  Finset.min'_le (Finset.univ.filter fun other => values other = values index) index
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

theorem firstOccurrence_eq_of_value_eq [DecidableEq α] (values : Fin size → α)
    (left right : Fin size) (hv : values left = values right) :
    firstOccurrence values left = firstOccurrence values right := by
  apply le_antisymm
  · exact Finset.min'_le (Finset.univ.filter fun other => values other = values left) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (firstOccurrence_value values right).trans hv.symm⟩)
  · exact Finset.min'_le (Finset.univ.filter fun other => values other = values right) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (firstOccurrence_value values left).trans hv⟩)

theorem firstOccurrence_isRoot [DecidableEq α] (values : Fin size → α) (index : Fin size) :
    IsRoot values (firstOccurrence values index) :=
  firstOccurrence_eq_of_value_eq values _ _ (firstOccurrence_value values index)

theorem firstOccurrence_pos [DecidableEq α] (values : Fin size → α)
    (last index : Fin size) (hvalue : values index ≠ values (initial last)) :
    0 < (firstOccurrence values index).val := by
  have hv := firstOccurrence_value values index
  by_contra hn
  have he : firstOccurrence values index = initial last := Fin.ext (by simp [initial]; omega)
  rw [he] at hv
  exact hvalue hv.symm

theorem first_positive_root [DecidableEq α] (values : Fin size → α)
    (last : Fin size) (hlast : 1 < last.val)
    (hinterior : ∀ index : Fin size, 0 < index.val → index < last →
      values index ≠ values (initial last)) :
    IsRoot values ⟨1, by omega⟩ := by
  let one : Fin size := ⟨1, by omega⟩
  have hp := firstOccurrence_pos values last one (hinterior one Nat.zero_lt_one hlast)
  have hl := firstOccurrence_le values one
  apply Fin.ext
  change (firstOccurrence values one).val = 1
  change (firstOccurrence values one).val ≤ 1 at hl
  omega

-- The middle interval has more positions than there are earlier root
-- positions. A repeated kind gives a recent copy; a new kind gives a root.
theorem exists_middle_of_lastRoot [DecidableEq α] (values : Fin size → α)
    (reach : Nat) (last prefetch : Fin size)
    (hr : 0 < reach) (hlong : reach < last.val) (hupper : last.val ≤ 2 * reach)
    (hp : 0 < prefetch.val)
    (hpFar : prefetch.val < last.val - reach)
    (hmax : ∀ index : Fin size, 0 < index.val → index.val ≤ reach →
      IsRoot values index → index ≤ prefetch)
    (hinterior : ∀ index : Fin size, 0 < index.val → index < last →
      values index ≠ values (initial last)) :
    ∃ index : Fin size, last.val - reach ≤ index.val ∧ index.val ≤ prefetch.val + reach ∧
      (IsRoot values index ∨ RecentCopy values (last.val - reach) index) := by
  let lower : Fin size := ⟨last.val - reach, by omega⟩
  let upper : Fin size := ⟨prefetch.val + reach, by omega⟩
  let middle := Finset.Icc lower upper
  let early := Finset.Icc (⟨1, by omega⟩ : Fin size) prefetch
  by_contra hn
  have hbad : ∀ index ∈ middle, ¬IsRoot values index ∧
      ¬RecentCopy values (last.val - reach) index := by
    intro index hi
    have hb := Finset.mem_Icc.mp hi
    constructor
    · intro hroot
      exact hn ⟨index, hb.1, hb.2, Or.inl hroot⟩
    · intro hcopy
      exact hn ⟨index, hb.1, hb.2, Or.inr hcopy⟩
  have hmap : ∀ index ∈ middle, firstOccurrence values index ∈ early := by
    intro index hi
    have hb := Finset.mem_Icc.mp hi
    have hbounds : last.val - reach ≤ index.val ∧ index.val ≤ prefetch.val + reach := hb
    have hposition : 0 < index.val ∧ index < last := by
      constructor
      · omega
      · change index.val < last.val
        omega
    have hfirstPos := firstOccurrence_pos values last index
      (hinterior index hposition.1 hposition.2)
    have hfirstLe := firstOccurrence_le values index
    have hfirstNe : firstOccurrence values index ≠ index := (hbad index hi).1
    have hfirstLt : firstOccurrence values index < index := lt_of_le_of_ne hfirstLe hfirstNe
    have hbefore : (firstOccurrence values index).val < last.val - reach := by
      by_contra hh
      exact (hbad index hi).2 ⟨firstOccurrence values index, by omega, hfirstLt,
        firstOccurrence_value values index⟩
    exact Finset.mem_Icc.mpr ⟨hfirstPos,
      hmax _ hfirstPos (by omega) (firstOccurrence_isRoot values index)⟩
  have hinj : Set.InjOn (firstOccurrence values) (middle : Set (Fin size)) := by
    intro left hl right hr he
    have hv : values left = values right :=
      (firstOccurrence_value values left).symm.trans
        ((congrArg values he).trans (firstOccurrence_value values right))
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hbad right hr).2 ⟨left, (Finset.mem_Icc.mp hl).1, hlt, hv⟩
    · exact (hbad left hl).2 ⟨right, (Finset.mem_Icc.mp hr).1, hgt, hv.symm⟩
  have hsub : middle.image (firstOccurrence values) ⊆ early := by
    intro index hi
    obtain ⟨other, ho, rfl⟩ := Finset.mem_image.mp hi
    exact hmap other ho
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj] at hc
  simp only [middle, early, Fin.card_Icc, lower, upper] at hc
  omega

-- Choose the last root in the first DUP window. If it cannot reach the
-- final position in one hop, the preceding pigeonhole lemma supplies an
-- intermediate slot. No recursive stack state is part of this predicate.
theorem exists_carrierSlots [DecidableEq α] (values : Fin size → α)
    (reach : Nat) (last : Fin size) (hr : 0 < reach)
    (hlong : reach < last.val) (hupper : last.val ≤ 2 * reach)
    (hinterior : ∀ index : Fin size, 0 < index.val → index < last →
      values index ≠ values (initial last)) :
    ∃ prefetch middle, CarrierSlots values reach last prefetch middle := by
  let roots := Finset.univ.filter fun index : Fin size =>
    0 < index.val ∧ index.val ≤ reach ∧ IsRoot values index
  have hn : roots.Nonempty := by
    refine ⟨⟨1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨Nat.zero_lt_one, hr, first_positive_root values last (by omega) hinterior⟩
  let prefetch := roots.max' hn
  have hp := (Finset.mem_filter.mp (Finset.max'_mem roots hn)).2
  have hmax : ∀ index : Fin size, 0 < index.val → index.val ≤ reach →
      IsRoot values index → index ≤ prefetch := by
    intro index hpos hreach hroot
    exact Finset.le_max' roots index (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, hreach, hroot⟩)
  by_cases hnear : last.val - reach ≤ prefetch.val
  · refine ⟨prefetch, none, hp.1, hp.2.1, hp.2.2, ?_, ?_⟩
    · change prefetch.val < last.val
      omega
    · omega
  · have hfar : prefetch.val < last.val - reach := by omega
    obtain ⟨middle, hlo, hhi, hkind⟩ :=
      exists_middle_of_lastRoot values reach last prefetch hr hlong hupper hp.1 hfar hmax hinterior
    refine ⟨prefetch, some middle, hp.1, hp.2.1, hp.2.2, ?_, ?_, ?_, ?_, hkind⟩
    · change prefetch.val < middle.val
      omega
    · change middle.val < last.val
      omega
    · omega
    · omega

theorem Family.exists_carrierSlots (hfamily : Family target reach last) :
    ∃ prefetch middle, CarrierSlots (fun index => target[index]) reach last prefetch middle :=
  OneGap.exists_carrierSlots _ reach last hfamily.1 hfamily.2.1 hfamily.2.2.1 hfamily.2.2.2.2.2.1

end Shuffler.Optimality.Collective.OneGap
