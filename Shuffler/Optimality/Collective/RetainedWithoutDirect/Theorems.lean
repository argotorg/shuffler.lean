import Shuffler.Optimality.Collective.RetainedWithoutDirect
import Shuffler.Optimality.Collective.InventoryBound.Theorems

namespace Shuffler.Optimality.Collective

theorem retainedWithoutDirect_subset_retained (trace : Trace spills source target)
    (hpop : trace.noPop) : retainedWithoutDirect trace ⊆ retained trace := by
  intro gap hg
  have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
  have he := (Finset.mem_filter.mp hg).2
  by_contra hm
  have hl := unretained_direct_increase trace hpop gap hp hm
  omega

theorem retainedWithoutDirect_feasible (trace : Trace spills source target)
    (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    FeasiblePaidIntervals source target (retainedWithoutDirect trace) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro cut hcut
  have hsub : ((retainedWithoutDirect trace).filter fun gap => gap.Crosses cut.val) ⊆
      ((retained trace).filter fun gap => gap.Crosses cut.val) := by
    intro gap hg
    exact Finset.mem_filter.mpr
      ⟨retainedWithoutDirect_subset_retained trace hpop (Finset.mem_filter.mp hg).1,
        (Finset.mem_filter.mp hg).2⟩
  have hc := Finset.card_le_card hsub
  have hr := retained_capacity trace hpop hsource hcut
  omega

theorem direct_increase_of_not_retainedWithoutDirect (trace : Trace spills source target)
    (gap : Interval target) (hpaid : gap.Paid source)
    (hgap : gap ∉ retainedWithoutDirect trace) :
    directBefore gap.value (gap.start.val + 1) trace <
      directBefore gap.value (gap.stop.val + 1) trace := by
  have hlt : gap.start.val < gap.stop.val := gap.property.1
  have hmono := directBefore_mono trace gap.value (show gap.start.val + 1 ≤ gap.stop.val + 1 by omega)
  have hne : directBefore gap.value (gap.start.val + 1) trace ≠
      directBefore gap.value (gap.stop.val + 1) trace := by
    intro he
    exact hgap (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpaid⟩, he⟩)
  omega

theorem omitted_without_direct_count_le (trace : Trace spills source target) (hpop : trace.noPop)
    (value : Value) : intervalCount (paidIntervals source target \ retainedWithoutDirect trace) value ≤
      Lineage.directCount value trace - if value ∈ source then 0 else 1 := by
  apply intervalCount_le_extraDirect trace hpop _ _ value
  intro gap hg
  have ho := Finset.mem_sdiff.mp hg
  exact direct_increase_of_not_retainedWithoutDirect trace gap (Finset.mem_filter.mp ho.1).2 ho.2

theorem omitted_without_direct_weight_le_generationSurcharge
    (costs : PrimitiveCosts) (weights : Weights) (trace : Trace spills source target)
    (hpop : trace.noPop) :
    intervalWeight (fun value => directPrice costs weights spills value - unitPrice costs weights spills value)
      (paidIntervals source target \ retainedWithoutDirect trace) ≤
        generationSurcharge costs weights target.toFinset trace := by
  rw [intervalWeight_eq_sum_counts, generationSurcharge]
  apply Finset.sum_le_sum
  intro value _
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left
    (directPrice costs weights spills value - unitPrice costs weights spills value)
    (omitted_without_direct_count_le trace hpop value)

end Shuffler.Optimality.Collective
