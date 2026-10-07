import Shuffler.Optimality.BirthPlacement.Realize.Settle
import Shuffler.Optimality.BirthPlacement.Realize.Introduce
import Shuffler.Placement.TraceInvariants

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation Shuffler.Placement

variable {spills : SpillSet} {target : Stack} {plan : Plan spills target} {height : Nat}

structure BuildState (plan : Plan spills target) (height : Nat) where
  height_le : height ≤ target.length
  permutation : Equiv.Perm (Fin target.length)
  built : BuiltTrace spills [] (prefixValues target permutation height)
    (prefixValues target plan.assignment height : Multiset Value)
  forward : ForwardBefore permutation height
  deadlines : BirthDeadlines 16 permutation
  unborn : ∀ index : Fin target.length, height ≤ index.val → permutation index = plan.assignment index
  count : built.trace.swapCount + arbitrarySwapCount permutation = arbitrarySwapCount plan.assignment

def BuildState.initial (plan : Plan spills target) : BuildState plan 0 where
  height_le := Nat.zero_le _
  permutation := plan.assignment
  built := ⟨.Lit [], trivial, rfl⟩
  forward := fun _ hi => by omega
  deadlines := plan.deadlines
  unborn := fun _ _ => rfl
  count := by simp [Trace.swapCount]

def BuildState.step (state : BuildState plan height) (hheight : height < target.length) :
    BuildState plan (height + 1) := by
  let top : Fin target.length := ⟨height, hheight⟩
  let current := prefixValues target state.permutation height
  let value := target[plan.assignment top]
  have hlen : current.length = height := by
    simp only [current, prefixValues_length, Nat.min_eq_left state.height_le]
  have hcount : current.count value = ((birthWord target plan.assignment).take height).count value := by
    have hb := state.built.trace.noPop_balance state.built.noPop
    rw [state.built.additions] at hb
    have hc := congrArg (Multiset.count value) hb
    simpa only [current, prefixValues, Multiset.coe_nil, zero_add, Multiset.coe_count] using hc
  have hfrozen : current.take (height - 16) = target.take (height - 16) :=
    prefixValues_frozen target state.permutation height state.height_le state.forward state.deadlines
  have havailable := physicallyAvailable_of_counts spills current target
    (birthWord target plan.assignment) height value (plan.method top) hlen hcount hfrozen
    (plan.available top)
  let birth := appendBirth spills current value (plan.method top) havailable
  have hvalue : target[state.permutation top] = value := by
    simp only [state.unborn top (by rfl), value]
  have hgrowth : current ++ [value] = prefixValues target state.permutation (height + 1) := by
    rw [prefixValues_succ target state.permutation height hheight, hvalue]
  let born : Trace spills current (prefixValues target state.permutation (height + 1)) :=
    hgrowth ▸ birth.val
  have hbornPop : born.noPop := (Trace.noPop_cast _ _).mpr birth.property.1
  have hbornAdd : born.additions = {value} := (Trace.additions_cast _ _).trans birth.property.2.1
  have hbornCount : born.swapCount = 0 := (swapCount_cast _ _).trans birth.property.2.2
  let placed := settleTrace spills target state.permutation top state.forward state.deadlines
  let combined := (state.built.trace.concat born).concat placed.trace
  have hpop : combined.noPop :=
    (state.built.trace.concat born).noPop_concat placed.trace
      (state.built.trace.noPop_concat born state.built.noPop hbornPop) placed.noPop
  have hadd : combined.additions =
      (prefixValues target plan.assignment (height + 1) : Multiset Value) := by
    rw [Trace.additions_concat, Trace.additions_concat, state.built.additions,
      hbornAdd, placed.additions, add_zero,
      prefixValues_succ target plan.assignment height hheight]
    rfl
  refine ⟨by omega, placed.permutation, ⟨combined, hpop, hadd⟩,
    placed.forward, placed.deadlines, ?_, ?_⟩
  · intro index hi
    exact (placed.above index (by change height < index.val; omega)).trans
      (state.unborn index (by omega))
  · change combined.swapCount + arbitrarySwapCount placed.permutation = _
    simp only [combined, swapCount_concat, hbornCount, Nat.add_zero]
    have hs := state.count
    have hp := placed.count
    omega

structure RealizedPlan (plan : Plan spills target) where
  built : BuiltTrace spills [] target (birthWord target plan.assignment : Multiset Value)
  count : built.trace.swapCount = arbitrarySwapCount plan.assignment

def BuildState.output (state : BuildState plan height) (hheight : ¬height < target.length) :
    RealizedPlan plan := by
  have he : height = target.length := by have := state.height_le; omega
  have hp : state.permutation = 1 := ForwardBefore.eq_one state.permutation (he ▸ state.forward)
  have ht : prefixValues target state.permutation height = target := by
    simp only [hp, he, prefixValues_one]
  have hm : (prefixValues target plan.assignment height : Multiset Value) =
      (birthWord target plan.assignment : Multiset Value) := by
    have hlen := birthWord_length target plan.assignment
    simp only [prefixValues, he, ← hlen, List.take_length]
  let result := state.built.cast rfl ht hm
  refine ⟨result, ?_⟩
  have hc : state.built.trace.swapCount = arbitrarySwapCount plan.assignment := by
    have h := state.count
    have hz : arbitrarySwapCount state.permutation = 0 := by rw [hp, arbitrarySwapCount_one]
    omega
  exact (built_cast_swapCount state.built rfl ht hm).trans hc

def BuildState.finish (height : Nat) (state : BuildState plan height) : RealizedPlan plan :=
  if hheight : height < target.length then BuildState.finish (height + 1) (state.step hheight)
  else state.output hheight
termination_by target.length - height

def realize (plan : Plan spills target) : RealizedPlan plan := BuildState.finish 0 (BuildState.initial plan)

theorem realize_swapCount_le_moved (plan : Plan spills target) :
    (realize plan).built.trace.swapCount ≤ plan.assignment.support.card := by
  rw [(realize plan).count]
  exact Nat.sub_le _ _

end Shuffler.Optimality.BirthPlacement
