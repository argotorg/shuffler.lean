import Shuffler.Optimality.BirthPlacement.SourcePlan.Theorems

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation Shuffler.Placement

variable {spills : SpillSet} {source target : Stack} {plan : SourcePlan spills source target}
  {height : Nat}

structure SourceBuildState (plan : SourcePlan spills source target) (height : Nat) where
  source_le : source.length ≤ height
  height_le : height ≤ target.length
  permutation : Equiv.Perm (Fin target.length)
  built : BuiltTrace spills source (prefixValues target permutation height)
    (plan.births.take (height - source.length) : Multiset Value)
  forward : ForwardBefore permutation height
  deadlines : BirthDeadlines 16 permutation
  unborn : ∀ index : Fin target.length, height ≤ index.val → permutation index = plan.assignment index
  count : built.trace.swapCount + arbitrarySwapCount permutation =
    sourcePotential plan.assignment source.length plan.source_length
  events : traceEvents built.trace = plan.events.take (height - source.length)

def SourceBuildState.initial (entry : SourceEntry plan) : SourceBuildState plan source.length := by
  have hm : (0 : Multiset Value) = (plan.births.take (source.length - source.length) : Multiset Value) := by
    simp
  let built := entry.built.cast rfl rfl hm
  refine ⟨le_refl _, plan.source_length, (SourcePrefix.run plan.assignment source.length).permutation,
    built, (SourcePrefix.run_spec plan.assignment source.length plan.source_length).1,
    SourcePrefix.run_deadlines plan.assignment plan.deadlines source.length plan.source_length,
    (SourcePrefix.run_spec plan.assignment source.length plan.source_length).2.1, ?_, ?_⟩
  · dsimp only [built]
    rw [built_cast_swapCount, entry.count]
    exact sourceEntryCost_add_remaining plan.assignment source.length plan.source_length
  · simp only [built, built_cast_events, Nat.sub_self, List.take_zero]
    exact traceEvents_empty entry.built.trace entry.built.additions

def SourceBuildState.step (state : SourceBuildState plan height) (hh : height < target.length) :
    SourceBuildState plan (height + 1) := by
  let top : Fin target.length := ⟨height, hh⟩
  let eventIndex : Fin (target.length - source.length) :=
    ⟨height - source.length, by have := state.source_le; omega⟩
  let current := prefixValues target state.permutation height
  let value := target[plan.assignment top]
  let method := plan.method eventIndex
  have hlen : current.length = height := by
    simp only [current, prefixValues_length, Nat.min_eq_left state.height_le]
  have hcount : current.count value = ((birthWord target plan.assignment).take height).count value := by
    have hb := state.built.trace.noPop_balance state.built.noPop
    rw [state.built.additions] at hb
    have hp := congrArg (fun stack : Stack => (stack : Multiset Value))
      (plan.prefix_balance height state.source_le)
    have he : (current : Multiset Value) = (prefixValues target plan.assignment height : Multiset Value) :=
      hb.trans (by simpa only [← Multiset.coe_add] using hp)
    simpa only [Multiset.coe_count, prefixValues] using congrArg (Multiset.count value) he
  have hfrozen : current.take (height - 16) = target.take (height - 16) :=
    prefixValues_frozen target state.permutation height state.height_le state.forward state.deadlines
  have hslot : sourceSlot source.length target.length plan.source_length eventIndex = top := by
    apply Fin.ext
    dsimp only [sourceSlot, eventIndex, top]
    have := state.source_le
    omega
  have havailable : BirthAvailable spills target (birthWord target plan.assignment) height value method := by
    have ha := plan.available eventIndex
    have hheight : source.length + eventIndex.val = height := by
      dsimp [eventIndex]
      have := state.source_le
      omega
    simpa only [hslot, hheight] using ha
  let birth := appendBirth spills current value method
    (physicallyAvailable_of_counts spills current target (birthWord target plan.assignment)
      height value method hlen hcount hfrozen havailable)
  have hvalue : target[state.permutation top] = value := by
    simp only [state.unborn top (by rfl), value]
  have hgrowth : current ++ [value] = prefixValues target state.permutation (height + 1) := by
    rw [prefixValues_succ target state.permutation height hh, hvalue]
  let born : Trace spills current (prefixValues target state.permutation (height + 1)) :=
    hgrowth ▸ birth.val
  have hbornPop : born.noPop := (Trace.noPop_cast _ _).mpr birth.property.1
  have hbornAdd : born.additions = {value} := (Trace.additions_cast _ _).trans birth.property.2.1
  have hbornCount : born.swapCount = 0 := (swapCount_cast _ _).trans birth.property.2.2.1
  have hbornEvents : traceEvents born = [(method, value)] :=
    (traceEvents_cast _ _).trans birth.property.2.2.2
  let placed := settleTrace spills target state.permutation top state.forward state.deadlines
  let combined := (state.built.trace.concat born).concat placed.trace
  have hpop : combined.noPop :=
    (state.built.trace.concat born).noPop_concat placed.trace
      (state.built.trace.noPop_concat born state.built.noPop hbornPop) placed.noPop
  have hadd : combined.additions = (plan.births.take (height + 1 - source.length) : Multiset Value) := by
    rw [Trace.additions_concat, Trace.additions_concat, state.built.additions,
      hbornAdd, placed.additions, add_zero, plan.births_take_succ height state.source_le hh]
    rfl
  refine ⟨by have := state.source_le; omega, by omega, placed.permutation, ⟨combined, hpop, hadd⟩,
    placed.forward, placed.deadlines, ?_, ?_, ?_⟩
  · intro index hi
    exact (placed.above index (by change height < index.val; omega)).trans
      (state.unborn index (by omega))
  · change combined.swapCount + arbitrarySwapCount placed.permutation = _
    simp only [combined, swapCount_concat, hbornCount, Nat.add_zero]
    have hs := state.count
    have hp := placed.count
    omega
  · simp only [combined, traceEvents_concat, state.events, hbornEvents,
      traceEvents_empty placed.trace placed.additions, List.append_nil]
    exact (plan.events_take_succ height state.source_le hh).symm

structure RealizedSourcePlan (plan : SourcePlan spills source target) where
  built : BuiltTrace spills source target (plan.births : Multiset Value)
  count : built.trace.swapCount = sourcePotential plan.assignment source.length plan.source_length
  events : traceEvents built.trace = plan.events

def SourceBuildState.output (state : SourceBuildState plan height) (hh : ¬height < target.length) :
    RealizedSourcePlan plan := by
  have he : height = target.length := by have := state.height_le; omega
  have hp : state.permutation = 1 := ForwardBefore.eq_one state.permutation (he ▸ state.forward)
  have ht : prefixValues target state.permutation height = target := by
    simp only [hp, he, prefixValues_one]
  have hm : (plan.births.take (height - source.length) : Multiset Value) =
      (plan.births : Multiset Value) := by
    simp only [he, ← plan.births_length, List.take_length]
  let result := state.built.cast rfl ht hm
  refine ⟨result, ?_, ?_⟩
  · have hc : state.built.trace.swapCount =
        sourcePotential plan.assignment source.length plan.source_length := by
      have h := state.count
      have hz : arbitrarySwapCount state.permutation = 0 := by rw [hp, arbitrarySwapCount_one]
      omega
    exact (built_cast_swapCount state.built rfl ht hm).trans hc
  · change traceEvents (state.built.cast rfl ht hm).trace = plan.events
    rw [built_cast_events, state.events, he]
    simp only [← plan.events_length, List.take_length]

def SourceBuildState.finish (height : Nat) (state : SourceBuildState plan height) :
    RealizedSourcePlan plan :=
  if hh : height < target.length then SourceBuildState.finish (height + 1) (state.step hh)
  else state.output hh
termination_by target.length - height

def realizeSourceFromEntry (entry : SourceEntry plan) : RealizedSourcePlan plan :=
  SourceBuildState.finish source.length (SourceBuildState.initial entry)

end Shuffler.Optimality.BirthPlacement
