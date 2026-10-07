import Shuffler.Optimality.Collective.Counts

namespace Shuffler.Optimality.Collective

theorem retained_subset_paid (trace : Trace spills source target) :
    retained trace ⊆ paidIntervals source target := by
  intro gap hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, retained_paid trace gap hg⟩

theorem retained_feasible (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) : FeasiblePaidIntervals source target (retained trace) :=
  ⟨retained_subset_paid trace, fun _ hcut => retained_capacity trace hpop hsource hcut⟩

theorem inventoryMaximum_upper (source target : Stack) (premium : Value → Nat) :
    UpperInventoryWeight source target premium (inventoryMaximum source target premium) := by
  intro selected hf
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hf.1, hf⟩

theorem inventoryMaximum_le_of_upper
    (h : UpperInventoryWeight source target premium bound) :
    inventoryMaximum source target premium ≤ bound := by
  apply Finset.sup_le
  intro selected hs
  exact h selected (Finset.mem_filter.mp hs).2

theorem inventory_weight_le_omitted_add_bound (trace : Trace spills source target)
    (hpop : trace.noPop) (hsource : source.length ≤ 17)
    (hbound : UpperInventoryWeight source target premium bound) :
    intervalWeight premium (paidIntervals source target) ≤
      intervalWeight premium (omitted trace) + bound := by
  have hsaved := hbound (retained trace) (retained_feasible trace hpop hsource)
  have he := Finset.sum_sdiff (f := fun gap : Interval target => premium gap.value)
    (retained_subset_paid trace)
  change intervalWeight premium (omitted trace) + intervalWeight premium (retained trace) =
    intervalWeight premium (paidIntervals source target) at he
  omega

theorem inventory_floor_le_generationSurcharge (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) (hsource : source.length ≤ 17)
    (hbound : UpperInventoryWeight source target
      (fun value => directPrice costs weights spills value - unitPrice costs weights spills value) bound) :
    intervalWeight (fun value => directPrice costs weights spills value -
      unitPrice costs weights spills value) (paidIntervals source target) - bound ≤
        generationSurcharge costs weights target.toFinset trace := by
  have hp := inventory_weight_le_omitted_add_bound trace hpop hsource hbound
  have hc := omitted_weight_le_generationSurcharge costs weights trace hpop
  omega

theorem inventoryFloor_le_generationSurcharge (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    inventoryFloor source target (fun value => directPrice costs weights spills value -
      unitPrice costs weights spills value) ≤ generationSurcharge costs weights target.toFinset trace :=
  inventory_floor_le_generationSurcharge costs weights trace hpop hsource
    (inventoryMaximum_upper source target _)

theorem baseline_add_swapCost_add_inventoryFloor_le_score
    (costs : PrimitiveCosts) (weights : Weights) (trace : Trace spills source target)
    (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    baseline costs weights spills source trace.additions + costs.swap.score weights * trace.swapCount +
      inventoryFloor source target (fun value => directPrice costs weights spills value -
        unitPrice costs weights spills value) ≤ (traceCost costs trace).score weights := by
  have hi := inventoryFloor_le_generationSurcharge costs weights trace hpop hsource
  have hc := baseline_add_swapCost_add_generationSurcharge_le_score costs weights target.toFinset trace hpop
  omega

theorem baseline_add_swapCost_add_inventoryFloor_le_score_of_eligible
    (costs : PrimitiveCosts) (weights : Weights) (trace : Trace spills source target)
    (he : Eligible missing trace) (hsource : source.length ≤ 17) :
    baseline costs weights spills source missing + costs.swap.score weights * trace.swapCount +
      inventoryFloor source target (fun value => directPrice costs weights spills value -
        unitPrice costs weights spills value) ≤ (traceCost costs trace).score weights := by
  rw [← he.2]
  exact baseline_add_swapCost_add_inventoryFloor_le_score costs weights trace he.1 hsource

end Shuffler.Optimality.Collective
