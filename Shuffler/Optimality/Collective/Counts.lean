import Shuffler.Optimality.Collective.Retention
import Shuffler.Optimality.Collective.InventoryBound
import Shuffler.Optimality.GenerationSurcharge.Theorems
import Mathlib.Order.Interval.Finset.Nat

namespace Shuffler.Optimality.Collective

open Shuffler.Placement Lineage

def omitted (trace : Trace spills source target) : Finset (Interval target) :=
  paidIntervals source target \ retained trace

theorem mem_source_or_direct_pos (trace : Trace spills source target) (hpop : trace.noPop)
    (value : Value) (hmem : value ∈ target) : value ∈ source ∨ 0 < directCount value trace := by
  induction trace with
  | Lit => exact Or.inl hmem
  | @Swap previous depth hlen hlo hhi trace ih =>
      exact ih hpop ((List.swap_perm previous _ _).mem_iff.mp hmem)
  | @Dup previous depth hlen hlo hhi trace ih =>
      apply ih hpop
      rcases List.mem_append.mp hmem with hm | hm
      · exact hm
      · have he := List.mem_singleton.mp hm
        rw [he]
        exact List.getElem_mem (by omega)
  | Pop _ _ => exact False.elim hpop
  | Push added hfree trace ih =>
      rcases List.mem_append.mp hmem with hm | hm
      · rcases ih hpop hm with hs | hd
        · exact Or.inl hs
        · exact Or.inr (by simp only [directCount]; omega)
      · have he := List.mem_singleton.mp hm
        right
        simp [directCount, he]
  | Load id hspill trace ih =>
      rcases List.mem_append.mp hmem with hm | hm
      · rcases ih hpop hm with hs | hd
        · exact Or.inl hs
        · exact Or.inr (by simp only [directCount]; omega)
      · have he := List.mem_singleton.mp hm
        right
        simp [directCount, he]

theorem Interval.stop_le_start_of_start_lt (left right : Interval target)
    (hv : left.value = right.value) (hlt : left.start < right.start) :
    left.stop ≤ right.start := by
  by_contra hnot
  have hr : right.start < left.stop := lt_of_not_ge hnot
  exact left.property.2.2 right.start hlt hr hv.symm

theorem directBefore_start_lower (trace : Trace spills source target) (hpop : trace.noPop)
    (gap : Interval target) :
    (if gap.value ∈ source then 0 else 1) ≤ directBefore gap.value (gap.start.val + 1) trace := by
  by_cases hs : gap.value ∈ source
  · simp only [hs, ite_true, Nat.zero_le]
  · simp only [hs, ite_false]
    have hi : gap.start.val < (target.take (gap.start.val + 1)).length := by
      simp only [List.length_take]
      have := gap.start.isLt
      omega
    have hm : gap.value ∈ target.take (gap.start.val + 1) := by
      have hv := List.getElem_mem hi
      rw [List.getElem_take] at hv
      exact hv
    rw [← takeHeight_take trace hpop] at hm
    have hd := mem_source_or_direct_pos (takeHeight (gap.start.val + 1 + 16) trace).before
      (takeHeight_noPop trace hpop).1 gap.value (List.mem_of_mem_take hm)
    exact (hd.resolve_left hs)

theorem intervalCount_le_extraDirect (trace : Trace spills source target) (hpop : trace.noPop)
    (selected : Finset (Interval target))
    (hchange : ∀ gap ∈ selected, directBefore gap.value (gap.start.val + 1) trace <
      directBefore gap.value (gap.stop.val + 1) trace)
    (value : Value) : intervalCount selected value ≤
      directCount value trace - if value ∈ source then 0 else 1 := by
  let gaps := selected.filter fun gap => gap.value = value
  let charge := fun gap : Interval target => directBefore value (gap.start.val + 1) trace
  have hincrease (gap : Interval target) (hg : gap ∈ gaps) :
      charge gap < directBefore value (gap.stop.val + 1) trace := by
    have hv := (Finset.mem_filter.mp hg).2
    simpa only [charge, hv] using hchange gap (Finset.mem_filter.mp hg).1
  have hstrict (left : Interval target) (hl : left ∈ gaps)
      (right : Interval target) (hr : right ∈ gaps) (horder : left.start < right.start) :
      charge left < charge right := by
    have hv : left.value = right.value :=
      (Finset.mem_filter.mp hl).2.trans (Finset.mem_filter.mp hr).2.symm
    have hstop := Interval.stop_le_start_of_start_lt left right hv horder
    have hmono := directBefore_mono trace value
      (Nat.add_le_add_right (show left.stop.val ≤ right.start.val from hstop) 1)
    exact (hincrease left hl).trans_le hmono
  have hinj : Set.InjOn charge (gaps : Set (Interval target)) := by
    intro left hl right hr he
    apply Interval.start_injective
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact (ne_of_lt (hstrict left hl right hr hlt)) he
    · exact (ne_of_lt (hstrict right hr left hl hgt)) he.symm
  have hsub : gaps.image charge ⊆
      Finset.Ico (if value ∈ source then 0 else 1) (directCount value trace) := by
    intro count hc
    obtain ⟨gap, hg, rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
    · have hv := (Finset.mem_filter.mp hg).2
      simpa only [charge, hv] using directBefore_start_lower trace hpop gap
    · exact (hincrease gap hg).trans_le (directBefore_le trace value _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj, Nat.card_Ico] at hc
  exact hc

theorem omitted_count_le (trace : Trace spills source target) (hpop : trace.noPop)
    (value : Value) : intervalCount (omitted trace) value ≤
      directCount value trace - if value ∈ source then 0 else 1 := by
  apply intervalCount_le_extraDirect trace hpop (omitted trace) _ value
  intro gap hg
  have ho := Finset.mem_sdiff.mp hg
  exact unretained_direct_increase trace hpop gap (Finset.mem_filter.mp ho.1).2 ho.2

theorem omitted_weight_le_generationSurcharge (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    intervalWeight (fun value => directPrice costs weights spills value -
      unitPrice costs weights spills value) (omitted trace) ≤
        generationSurcharge costs weights target.toFinset trace := by
  rw [intervalWeight_eq_sum_counts, generationSurcharge]
  apply Finset.sum_le_sum
  intro value _
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left
    (directPrice costs weights spills value - unitPrice costs weights spills value)
    (omitted_count_le trace hpop value)

end Shuffler.Optimality.Collective
