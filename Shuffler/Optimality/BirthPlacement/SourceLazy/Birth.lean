import Shuffler.Optimality.BirthPlacement.SourceLazy.Phase

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

variable {spills : SpillSet} {source target : Stack}
  {plan : SourcePlan spills source target} {height : Nat}

theorem Result.values_count (state : State plan height) (result : Result plan height state)
    (value : Value) :
    state.values.count value = ((birthWord target plan.assignment).take height).count value := by
  have hb := result.built.trace.noPop_balance result.built.noPop
  rw [result.built.additions] at hb
  have hp := congrArg (fun stack : Stack => (stack : Multiset Value))
    (plan.prefix_balance height state.source_le)
  have he : (state.values : Multiset Value) =
      (prefixValues target plan.assignment height : Multiset Value) :=
    hb.trans (by simpa only [← Multiset.coe_add] using hp)
  simpa only [Multiset.coe_count, prefixValues] using congrArg (Multiset.count value) he

-- Append the chosen birth, then execute the checked permutation phase.
def Result.extend (top : Fin target.length) (state : State plan (top.val + 1))
    (phase : Phase top state) (prior : Result plan top.val phase.before) :
    Result plan (top.val + 1) state := by
  let eventIndex : Fin (target.length - source.length) :=
    ⟨top.val - source.length, by have := phase.before.source_le; have := top.isLt; omega⟩
  let value := target[plan.assignment top]
  let method := plan.method eventIndex
  have hslot : sourceSlot source.length target.length plan.source_length eventIndex = top := by
    apply Fin.ext
    dsimp only [sourceSlot, eventIndex]
    have := phase.before.source_le
    omega
  have hheight : source.length + eventIndex.val = top.val := by
    dsimp only [eventIndex]
    have := phase.before.source_le
    omega
  have havailable : BirthAvailable spills target (birthWord target plan.assignment)
      top.val value method := by
    simpa only [hheight, hslot, value, method] using plan.available eventIndex
  have hphysical := physicallyAvailable_of_counts spills phase.before.values target
    (birthWord target plan.assignment) top.val value method
    phase.before.values_length (prior.values_count phase.before value)
    phase.before.values_frozen havailable
  let birth := appendBirth spills phase.before.values value method hphysical
  have htop : phase.before.remaining⁻¹ top = top := by
    apply Equiv.Perm.inv_eq_iff_eq.mpr
    exact (phase.before.above top (Nat.le_refl _)).symm
  have hgrowth : phase.before.values ++ [value] =
      prefixValues target (plan.assignment * phase.before.remaining⁻¹) (top.val + 1) := by
    rw [prefixValues_succ target (plan.assignment * phase.before.remaining⁻¹) top.val top.isLt]
    simp only [Equiv.Perm.mul_apply, htop]
    rfl
  let born : Trace spills phase.before.values
      (prefixValues target (plan.assignment * phase.before.remaining⁻¹) (top.val + 1)) :=
    hgrowth ▸ birth.val
  have hbornPop : born.noPop := (Trace.noPop_cast _ _).mpr birth.property.1
  have hbornAdd : born.additions = {value} := (Trace.additions_cast _ _).trans birth.property.2.1
  have hbornCount : born.swapCount = 0 := (swapCount_cast _ _).trans birth.property.2.2.1
  have hbornEvents : traceEvents born = [(method, value)] :=
    (traceEvents_cast _ _).trans birth.property.2.2.2
  let combined := (prior.built.trace.concat born).concat phase.built.trace
  have hpop : combined.noPop :=
    (prior.built.trace.concat born).noPop_concat phase.built.trace
      (prior.built.trace.noPop_concat born prior.built.noPop hbornPop) phase.built.noPop
  have hadd : combined.additions =
      (plan.births.take (top.val + 1 - source.length) : Multiset Value) := by
    rw [Trace.additions_concat, Trace.additions_concat, prior.built.additions,
      hbornAdd, phase.built.additions, add_zero,
      plan.births_take_succ top.val phase.before.source_le top.isLt]
    rfl
  refine ⟨⟨combined, hpop, hadd⟩, ?_, ?_⟩
  · change combined.swapCount = _
    simp only [combined, swapCount_concat, hbornCount, Nat.add_zero, prior.count]
    have hc := phase.count
    omega
  · change traceEvents combined = _
    simp only [combined, traceEvents_concat, prior.events, hbornEvents,
      traceEvents_empty phase.built.trace phase.built.additions, List.append_nil]
    exact (plan.events_take_succ top.val phase.before.source_le top.isLt).symm

end Shuffler.Optimality.BirthPlacement.SourceLazy
