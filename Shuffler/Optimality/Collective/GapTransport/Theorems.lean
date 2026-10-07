import Shuffler.Optimality.Collective.GapTransport
import Shuffler.Optimality.Collective.RetainedWithoutDirect.Theorems
import Shuffler.Optimality.Transport.Sparse.Theorems

namespace Shuffler.Optimality.Collective

open Lineage Transport

theorem upwardCount_concat (first : Trace spills source middle)
    (second : Trace spills middle target) (value : Value) :
    upwardCount value (first.concat second) = upwardCount value first + upwardCount value second := by
  induction second with
  | Lit => simp [Trace.concat, upwardCount]
  | Swap _ _ _ _ trace ih => simp only [Trace.concat, upwardCount, ih, Nat.add_assoc]
  | Dup _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      exact ih

theorem upwardBefore_le (trace : Trace spills source target) (value : Value) (cut : Nat) :
    upwardBefore value cut trace ≤ upwardCount value trace := by
  have he := congrArg (upwardCount value) (takeHeight_joined (height := cut + 16) trace)
  rw [upwardCount_concat] at he
  exact Nat.le.intro he

theorem upwardBefore_mono (trace : Trace spills source target) (value : Value)
    (horder : low ≤ high) : upwardBefore value low trace ≤ upwardBefore value high trace := by
  have he := congrArg (fun part : (current : Stack) × Trace spills source current =>
    upwardCount value part.2) (takeHeight_nested trace (Nat.add_le_add_right horder 16))
  have hl := upwardBefore_le (takeHeight (high + 16) trace).before value low
  change upwardBefore value low (takeHeight (high + 16) trace).before =
    upwardBefore value low trace at he
  change upwardBefore value low (takeHeight (high + 16) trace).before ≤
    upwardBefore value high trace at hl
  omega

theorem sparsePotential_between_cuts (trace : Trace spills source target) (hpop : trace.noPop)
    (residue : Fin 16) (value : Value) (goal : Stack) (horder : low ≤ high) :
    sparsePotential residue value goal (takeHeight (low + 16) trace).current +
        upwardBefore value low trace ≤
      sparsePotential residue value goal (takeHeight (high + 16) trace).current +
        upwardBefore value high trace := by
  let highPart := takeHeight (high + 16) trace
  let lowPart := takeHeight (low + 16) highPart.before
  have hn := takeHeight_nested trace (Nat.add_le_add_right horder 16)
  have hc := congrArg Sigma.fst hn
  change lowPart.current = (takeHeight (low + 16) trace).current at hc
  have hu := congrArg (fun part : (current : Stack) × Trace spills source current =>
    upwardCount value part.2) hn
  change upwardCount value lowPart.before = upwardBefore value low trace at hu
  have hp := (takeHeight_noPop (height := high + 16) trace hpop).1
  have hlp := (takeHeight_noPop (height := low + 16) highPart.before hp).2
  have hs := sparsePotential_source_le residue value goal lowPart.after hlp
  have hj := congrArg (upwardCount value)
    (takeHeight_joined (height := low + 16) highPart.before)
  rw [upwardCount_concat] at hj
  change upwardCount value lowPart.before + upwardCount value lowPart.after =
    upwardBefore value high trace at hj
  have he := congrArg (sparsePotential residue value goal) hc
  change sparsePotential residue value goal lowPart.current ≤
    sparsePotential residue value goal (takeHeight (high + 16) trace).current +
      upwardCount value lowPart.after at hs
  omega

theorem sparsePotential_eq_zero_of_take_eq (residue : Fin 16) (value : Value)
    (goal stack : Stack) (he : stack.take goal.length = goal) :
    sparsePotential residue value goal stack = 0 := by
  apply Finset.sum_eq_zero
  intro cut hc
  have hl : cut + 1 ≤ goal.length := by have := Finset.mem_range.mp hc; omega
  have ht := congrArg (List.take (cut + 1)) he
  simp only [List.take_take, Nat.min_eq_left hl] at ht
  simp [surplus, ht]

-- The argument permits arbitrary births, including anticipatory DUPs.
-- Each selected prefix starts with an extra copy, and births cannot remove it.
theorem gap_sparse_demand (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (gap : Interval target)
    (hresident : gap.value ∈ residual (gap.start.val + 1) trace) :
    gap.transportDemand ≤
      sparsePotential ⟨gap.start.val % 16, Nat.mod_lt _ (by decide)⟩ gap.value
        (target.take gap.stop.val) (takeHeight (gap.start.val + 1 + 16) trace).current := by
  let state := (takeHeight (gap.start.val + 1 + 16) trace).current
  let mark := fun index : Nat => gap.start.val + 16 * (index + 1)
  let marks := (Finset.range gap.transportDemand).image mark
  have hlength : state.length ≤ gap.start.val + 17 := by
    have he := takeHeight_length (height := gap.start.val + 1 + 16) trace hpop (by omega)
    change state.length = _ at he
    omega
  have hpositive : (target.take (gap.start.val + 1)).count gap.value < state.count gap.value := by
    have hp : 0 < (state.drop (gap.start.val + 1)).count gap.value :=
      List.count_pos_iff.mpr hresident
    have he := congrArg (List.count gap.value) (List.take_append_drop (gap.start.val + 1) state)
    simp only [List.count_append] at he
    have ht := takeHeight_take (cut := gap.start.val + 1) trace hpop
    change state.take (gap.start.val + 1) = _ at ht
    rw [ht] at he
    omega
  have hmarks (cut : Nat) (hc : cut ∈ marks) :
      gap.start.val + 16 ≤ cut ∧ cut < gap.stop.val ∧ cut % 16 = gap.start.val % 16 := by
    obtain ⟨index, hi, rfl⟩ := Finset.mem_image.mp hc
    have hid := Finset.mem_range.mp hi
    have hlt : gap.start.val < gap.stop.val := gap.property.1
    dsimp only [Interval.transportDemand] at hid
    dsimp only [mark]
    omega
  have hsub : marks ⊆ Finset.range (target.take gap.stop.val).length := by
    intro cut hc
    have hm := hmarks cut hc
    simp only [List.length_take, Finset.mem_range]
    have := gap.stop.isLt
    omega
  have hcard : marks.card = gap.transportDemand := by
    rw [Finset.card_image_iff.mpr]
    · exact Finset.card_range _
    · intro left _ right _ he
      dsimp only [mark] at he
      omega
  calc
    gap.transportDemand = marks.sum (fun _ => 1) := by simp [hcard]
    _ ≤ marks.sum (fun cut =>
        if cut % 16 = gap.start.val % 16 then
          surplus gap.value (target.take gap.stop.val) state cut else 0) := by
      apply Finset.sum_le_sum
      intro cut hc
      obtain ⟨hlo, hhi, hmod⟩ := hmarks cut hc
      have ht : state.take (cut + 1) = state := List.take_of_length_le (by omega)
      have hcount := gap.count_take_eq (cut := cut + 1) ⟨by omega, by omega⟩
      simp only [hmod, ite_true, surplus, ht, List.take_take,
        Nat.min_eq_left (show cut + 1 ≤ gap.stop.val by omega)]
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)

theorem gap_transport_le_upward_between (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (gap : Interval target)
    (hresident : gap.value ∈ residual (gap.start.val + 1) trace) :
    gap.transportDemand + upwardBefore gap.value (gap.start.val + 1) trace ≤
      upwardBefore gap.value (gap.stop.val + 1) trace := by
  let residue : Fin 16 := ⟨gap.start.val % 16, Nat.mod_lt _ (by decide)⟩
  have hlt : gap.start.val < gap.stop.val := gap.property.1
  have hs := sparsePotential_between_cuts trace hpop residue gap.value (target.take gap.stop.val)
    (low := gap.start.val + 1) (high := gap.stop.val + 1) (by omega)
  have hz : sparsePotential residue gap.value (target.take gap.stop.val)
      (takeHeight (gap.stop.val + 1 + 16) trace).current = 0 := by
    apply sparsePotential_eq_zero_of_take_eq
    have ht := congrArg (List.take gap.stop.val) (takeHeight_take (cut := gap.stop.val + 1) trace hpop)
    simpa only [List.take_take, Nat.min_eq_left (show gap.stop.val ≤ gap.stop.val + 1 by omega),
      List.length_take, Nat.min_eq_left (Nat.le_of_lt gap.stop.isLt)] using ht
  have hd := gap_sparse_demand trace hpop hsource gap hresident
  change gap.transportDemand ≤ sparsePotential residue _ _ _ at hd
  omega

theorem gapTransport_value_add_le (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (selected : Finset (Interval target))
    (hresident : ∀ gap ∈ selected, gap.value ∈ residual (gap.start.val + 1) trace)
    (value : Value) (initial : Nat) (hinitial : initial ≤ upwardCount value trace)
    (hstart : ∀ gap ∈ selected, gap.value = value →
      initial ≤ upwardBefore value (gap.start.val + 1) trace) :
    gapTransport (selected.filter fun gap => gap.value = value) + initial ≤
      upwardCount value trace := by
  let gaps := selected.filter fun gap => gap.value = value
  let levels := fun gap : Interval target =>
    Finset.Ico (upwardBefore value (gap.start.val + 1) trace)
      (upwardBefore value (gap.stop.val + 1) trace)
  have hdisjoint : (gaps : Set (Interval target)).PairwiseDisjoint levels := by
    intro left hl right hr hne
    have hvl := (Finset.mem_filter.mp hl).2
    have hvr := (Finset.mem_filter.mp hr).2
    have hn : left.start ≠ right.start := fun he => hne (Interval.start_injective he)
    apply Finset.disjoint_left.mpr
    intro level hll hrl
    have hleft := Finset.mem_Ico.mp hll
    have hright := Finset.mem_Ico.mp hrl
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hstop := Interval.stop_le_start_of_start_lt left right (hvl.trans hvr.symm) hlt
      have hm := upwardBefore_mono trace value
        (Nat.add_le_add_right (show left.stop.val ≤ right.start.val from hstop) 1)
      omega
    · have hstop := Interval.stop_le_start_of_start_lt right left (hvr.trans hvl.symm) hgt
      have hm := upwardBefore_mono trace value
        (Nat.add_le_add_right (show right.stop.val ≤ left.start.val from hstop) 1)
      omega
  have hsub : gaps.biUnion levels ⊆ Finset.Ico initial (upwardCount value trace) := by
    intro level hl
    obtain ⟨gap, hg, hm⟩ := Finset.mem_biUnion.mp hl
    have hb := Finset.mem_Ico.mp hm
    have hst := hstart gap (Finset.mem_filter.mp hg).1 (Finset.mem_filter.mp hg).2
    have hstop := upwardBefore_le trace value (gap.stop.val + 1)
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisjoint, Nat.card_Ico] at hc
  have hd : gapTransport gaps ≤ gaps.sum (fun gap => (levels gap).card) := by
    apply Finset.sum_le_sum
    intro gap hg
    have hr := hresident gap (Finset.mem_filter.mp hg).1
    have ht := gap_transport_le_upward_between trace hpop hsource gap hr
    rw [(Finset.mem_filter.mp hg).2] at ht
    change gap.transportDemand ≤ (Finset.Ico _ _).card
    rw [Nat.card_Ico]
    omega
  change gapTransport gaps + initial ≤ _
  omega

theorem gapTransport_value_le (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (selected : Finset (Interval target))
    (hresident : ∀ gap ∈ selected, gap.value ∈ residual (gap.start.val + 1) trace)
    (value : Value) :
    gapTransport (selected.filter fun gap => gap.value = value) ≤ upwardCount value trace := by
  simpa only [Nat.add_zero] using gapTransport_value_add_le trace hpop hsource selected hresident
    value 0 (Nat.zero_le _) (by intros; exact Nat.zero_le _)

theorem gapTransport_eq_sum_values (selected : Finset (Interval target)) :
    gapTransport selected = target.toFinset.sum (fun value =>
      gapTransport (selected.filter fun gap => gap.value = value)) := by
  have hm : ∀ gap ∈ selected, gap.value ∈ target.toFinset := by
    intro gap _
    exact List.mem_toFinset.mpr gap.value_mem
  exact (Finset.sum_fiberwise_of_maps_to hm _).symm

theorem gapTransport_le_swapCount (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (selected : Finset (Interval target))
    (hresident : ∀ gap ∈ selected, gap.value ∈ residual (gap.start.val + 1) trace) :
    gapTransport selected ≤ trace.swapCount := by
  rw [gapTransport_eq_sum_values]
  apply le_trans (Finset.sum_le_sum (fun value _ =>
    gapTransport_value_le trace hpop hsource selected hresident value))
  exact Lineage.sum_upwardCount_le _ trace

theorem retained_gapTransport_le_swapCount (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) : gapTransport (retained trace) ≤ trace.swapCount := by
  apply gapTransport_le_swapCount trace hpop hsource
  intro gap hg
  exact (Finset.mem_filter.mp hg).2.2

theorem retainedWithoutDirect_gapTransport_le_swapCount (trace : Trace spills source target)
    (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    gapTransport (retainedWithoutDirect trace) ≤ trace.swapCount := by
  apply gapTransport_le_swapCount trace hpop hsource
  intro gap hg
  exact (Finset.mem_filter.mp (retainedWithoutDirect_subset_retained trace hpop hg)).2.2

theorem sparsePotential_take_eq_of_count_le (residue : Fin 16) (value : Value)
    (source target : Stack) (cut : Nat) (hcut : cut ≤ target.length)
    (hcount : source.count value ≤ (target.take cut).count value) :
    sparsePotential residue value target source =
      sparsePotential residue value (target.take cut) source := by
  let term := fun index => if index % 16 = residue.val then surplus value target source index else 0
  have hsub : Finset.range cut ⊆ Finset.range target.length := Finset.range_mono hcut
  have hsum : (Finset.range cut).sum term = (Finset.range target.length).sum term := by
    apply Finset.sum_subset hsub
    intro index _ hn
    have hi : cut ≤ index := by simpa only [Finset.mem_range, not_lt] using hn
    have hs : (source.take (index + 1)).count value ≤ source.count value :=
      (List.take_sublist _ _).count_le _
    have ht : (target.take cut).count value ≤ (target.take (index + 1)).count value :=
      (List.take_sublist_take_left (by omega)).count_le _
    dsimp only [term, surplus]
    split_ifs
    · omega
    · rfl
  change (Finset.range target.length).sum term = _
  rw [← hsum]
  unfold sparsePotential
  rw [List.length_take, Nat.min_eq_left hcut]
  apply Finset.sum_congr rfl
  intro index hi
  have hl : index + 1 ≤ cut := by have := Finset.mem_range.mp hi; omega
  simp only [term, surplus, List.take_take, Nat.min_eq_left hl]

theorem old_sparse_le_upwardBefore (trace : Trace spills source target) (hpop : trace.noPop)
    (residue : Fin 16) (value : Value) (cut : Nat) (hcut : cut ≤ target.length)
    (hcount : source.count value ≤ (target.take cut).count value) :
    sparsePotential residue value target source ≤ upwardBefore value cut trace := by
  have hs := sparsePotential_source_le residue value (target.take cut)
    (takeHeight (cut + 16) trace).before (takeHeight_noPop trace hpop).1
  have hz : sparsePotential residue value (target.take cut)
      (takeHeight (cut + 16) trace).current = 0 := by
    apply sparsePotential_eq_zero_of_take_eq
    simpa only [List.length_take, Nat.min_eq_left hcut] using takeHeight_take (cut := cut) trace hpop
  rw [hz, Nat.zero_add] at hs
  rw [sparsePotential_take_eq_of_count_le residue value source target cut hcut hcount]
  exact hs

theorem old_transport_le_upwardBefore (trace : Trace spills source target) (hpop : trace.noPop)
    (value : Value) (cut : Nat) (hcut : cut ≤ target.length)
    (hcount : source.count value ≤ (target.take cut).count value) :
    sparseRequiredSwaps value source target ≤ upwardBefore value cut trace := by
  apply Finset.sup_le
  intro residue _
  exact old_sparse_le_upwardBefore trace hpop residue value cut hcut hcount

theorem old_add_gapTransport_value_le (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source)
    (hresident : ∀ gap ∈ selected, gap.value ∈ residual (gap.start.val + 1) trace)
    (value : Value) :
    sparseRequiredSwaps value source target +
      gapTransport (selected.filter fun gap => gap.value = value) ≤ upwardCount value trace := by
  rw [Nat.add_comm]
  apply gapTransport_value_add_le trace hpop hsource selected hresident value _
    (sparseRequiredSwaps_le_upwardCount value trace hpop)
  intro gap hg hv
  apply old_transport_le_upwardBefore trace hpop value (gap.start.val + 1)
    (by have := gap.start.isLt; omega)
  simpa only [Interval.Paid, hv] using hpaid gap hg

theorem old_add_gapTransport_le_swapCount (trace : Trace spills source target) (hpop : trace.noPop)
    (hsource : source.length ≤ 17) (selected : Finset (Interval target))
    (hpaid : ∀ gap ∈ selected, gap.Paid source)
    (hresident : ∀ gap ∈ selected, gap.value ∈ residual (gap.start.val + 1) trace) :
    (target.toFinset.sum fun value => sparseRequiredSwaps value source target) +
      gapTransport selected ≤ trace.swapCount := by
  rw [gapTransport_eq_sum_values, ← Finset.sum_add_distrib]
  apply le_trans (Finset.sum_le_sum (fun value _ =>
    old_add_gapTransport_value_le trace hpop hsource selected hpaid hresident value))
  exact Lineage.sum_upwardCount_le _ trace

theorem old_add_retained_gapTransport_le_swapCount (trace : Trace spills source target)
    (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    (target.toFinset.sum fun value => sparseRequiredSwaps value source target) +
      gapTransport (retained trace) ≤ trace.swapCount := by
  apply old_add_gapTransport_le_swapCount trace hpop hsource _ (retained_paid trace)
  intro gap hg
  exact (Finset.mem_filter.mp hg).2.2

theorem old_add_retainedWithoutDirect_gapTransport_le_swapCount (trace : Trace spills source target)
    (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    (target.toFinset.sum fun value => sparseRequiredSwaps value source target) +
      gapTransport (retainedWithoutDirect trace) ≤ trace.swapCount := by
  apply old_add_gapTransport_le_swapCount trace hpop hsource
  · intro gap hg
    exact retained_paid trace gap (retainedWithoutDirect_subset_retained trace hpop hg)
  · intro gap hg
    exact (Finset.mem_filter.mp (retainedWithoutDirect_subset_retained trace hpop hg)).2.2

theorem baseline_add_retained_jointPlanCost_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    baseline costs weights spills source trace.additions +
      jointPlanCost costs weights spills source target (retained trace) ≤
        (traceCost costs trace).score weights := by
  have hs := baseline_add_swapCost_add_generationSurcharge_le_score costs weights target.toFinset trace hpop
  have hi := omitted_weight_le_generationSurcharge costs weights trace hpop
  have hm := Nat.mul_le_mul_left (costs.swap.score weights)
    (old_add_retained_gapTransport_le_swapCount trace hpop hsource)
  unfold jointPlanCost oldTransport
  change intervalWeight _ (paidIntervals source target \ retained trace) ≤ _ at hi
  omega

theorem baseline_add_retainedWithoutDirect_jointPlanCost_le_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    baseline costs weights spills source trace.additions +
      jointPlanCost costs weights spills source target (retainedWithoutDirect trace) ≤
        (traceCost costs trace).score weights := by
  have hs := baseline_add_swapCost_add_generationSurcharge_le_score costs weights target.toFinset trace hpop
  have hi := omitted_without_direct_weight_le_generationSurcharge costs weights trace hpop
  have hm := Nat.mul_le_mul_left (costs.swap.score weights)
    (old_add_retainedWithoutDirect_gapTransport_le_swapCount trace hpop hsource)
  unfold jointPlanCost oldTransport
  omega

theorem exists_feasible_jointPlan (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) (hsource : source.length ≤ 17) :
    ∃ selected : Finset (Interval target), FeasiblePaidIntervals source target selected ∧
      baseline costs weights spills source trace.additions +
        jointPlanCost costs weights spills source target selected ≤ (traceCost costs trace).score weights :=
  ⟨retainedWithoutDirect trace, retainedWithoutDirect_feasible trace hpop hsource,
    baseline_add_retainedWithoutDirect_jointPlanCost_le_score costs weights trace hpop hsource⟩

end Shuffler.Optimality.Collective
