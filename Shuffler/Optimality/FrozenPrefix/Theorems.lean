import Shuffler.Optimality.FrozenPrefix.Trace

namespace Shuffler.Optimality.FrozenPrefix

open Shuffler.Placement

theorem cost_eq_of_flatten_eq (costs : PrimitiveCosts)
    (first : Trace spills source target) (second : Trace otherSpills otherSource otherTarget)
    (h : flatten first = flatten second) : traceCost costs first = traceCost costs second := by
  rw [← opsCost_flatten, ← opsCost_flatten, h]

theorem exists_drop_eligible (trace : Trace spills source target)
    (he : Eligible missing trace) (count : Nat) (hcount : count ≤ frozen source) :
    ∃ reduced : Trace spills (source.drop count) (target.drop count),
      Eligible missing reduced ∧ flatten reduced = flatten trace ∧
        ∀ costs, traceCost costs reduced = traceCost costs trace := by
  obtain ⟨reduced, hp, ha, ho⟩ := exists_drop trace he.1 count hcount
  exact ⟨reduced, ⟨hp, ha.trans he.2⟩, ho, fun costs => cost_eq_of_flatten_eq costs _ _ ho⟩

theorem exists_lift_eligible (trace : Trace spills source target)
    (he : Eligible missing trace) (fixed : Stack) :
    ∃ lifted : Trace spills (fixed ++ source) (fixed ++ target),
      Eligible missing lifted ∧ flatten lifted = flatten trace ∧
        ∀ costs, traceCost costs lifted = traceCost costs trace := by
  obtain ⟨lifted, hp, ha, ho⟩ := exists_lift trace he.1 fixed
  exact ⟨lifted, ⟨hp, ha.trans he.2⟩, ho, fun costs => cost_eq_of_flatten_eq costs _ _ ho⟩

private theorem prefix_eq (trace : Trace spills source target) (hpop : trace.noPop)
    (count : Nat) (hcount : count ≤ frozen source) :
    target.take count = source.take count := by
  have h := congrArg (List.take count) (trace.noPop_frozen hpop)
  simpa only [List.take_take, Nat.min_eq_left hcount] using h

-- The matching-prefix condition is necessary. It is the only condition
-- added to the reduced trace problem. The spill set and additions stay fixed.
theorem exists_operations_iff (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) (count : Nat) (hcount : count ≤ frozen source)
    (ops : List Op) :
    (∃ trace : Trace spills source target, Eligible missing trace ∧ flatten trace = ops) ↔
      target.take count = source.take count ∧
        ∃ reduced : Trace spills (source.drop count) (target.drop count),
          Eligible missing reduced ∧ flatten reduced = ops := by
  constructor
  · rintro ⟨trace, he, ho⟩
    obtain ⟨reduced, hr, hro, _⟩ := exists_drop_eligible trace he count hcount
    exact ⟨prefix_eq trace he.1 count hcount, reduced, hr, hro.trans ho⟩
  · rintro ⟨hp, reduced, hr, ho⟩
    have htarget : source.take count ++ target.drop count = target := by
      rw [← hp, List.take_append_drop]
    have h : ∃ lifted : Trace spills (source.take count ++ source.drop count)
        (source.take count ++ target.drop count), Eligible missing lifted ∧ flatten lifted = ops := by
      obtain ⟨lifted, he, hlo, _⟩ := exists_lift_eligible reduced hr (source.take count)
      exact ⟨lifted, he, hlo.trans ho⟩
    rw [List.take_append_drop, htarget] at h
    exact h

-- Thus the full problem and the reduced problem have the same attainable
-- gas/byte pairs under every primitive cost model.
theorem exists_cost_iff (costs : PrimitiveCosts) (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) (count : Nat) (hcount : count ≤ frozen source)
    (cost : Cost) :
    (∃ trace : Trace spills source target, Eligible missing trace ∧ traceCost costs trace = cost) ↔
      target.take count = source.take count ∧
        ∃ reduced : Trace spills (source.drop count) (target.drop count),
          Eligible missing reduced ∧ traceCost costs reduced = cost := by
  constructor
  · rintro ⟨trace, he, hc⟩
    obtain ⟨reduced, hr, _, hcost⟩ := exists_drop_eligible trace he count hcount
    exact ⟨prefix_eq trace he.1 count hcount, reduced, hr, (hcost costs).trans hc⟩
  · rintro ⟨hp, reduced, hr, hc⟩
    have htarget : source.take count ++ target.drop count = target := by
      rw [← hp, List.take_append_drop]
    have h : ∃ lifted : Trace spills (source.take count ++ source.drop count)
        (source.take count ++ target.drop count),
        Eligible missing lifted ∧ traceCost costs lifted = cost := by
      obtain ⟨lifted, he, _, hlc⟩ := exists_lift_eligible reduced hr (source.take count)
      exact ⟨lifted, he, (hlc costs).trans hc⟩
    rw [List.take_append_drop, htarget] at h
    exact h

theorem score_lower_bound_of_drop (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (he : Eligible missing trace)
    (count : Nat) (hcount : count ≤ frozen source) (bound : Nat)
    (hbound : ∀ reduced : Trace spills (source.drop count) (target.drop count),
      Eligible missing reduced → bound ≤ (traceCost costs reduced).score weights) :
    bound ≤ (traceCost costs trace).score weights := by
  obtain ⟨reduced, hr, _, hc⟩ := exists_drop_eligible trace he count hcount
  simpa only [hc costs] using hbound reduced hr

theorem exists_window_eligible (trace : Trace spills source target)
    (he : Eligible missing trace) :
    ∃ reduced : Trace spills (window source) (target.drop (frozen source)),
      Eligible missing reduced ∧ flatten reduced = flatten trace ∧
        ∀ costs, traceCost costs reduced = traceCost costs trace :=
  exists_drop_eligible trace he (frozen source) (Nat.le_refl _)

end Shuffler.Optimality.FrozenPrefix
