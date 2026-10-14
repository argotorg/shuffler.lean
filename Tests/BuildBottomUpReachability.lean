import Shuffler

open Shuffler.BuildBottomUp

set_option maxRecDepth 16384

-- State.reachable unfolds to this condition: each unbound target value can be freely generated, is
-- spilled, or has a copy in DUP reach.
example (state : State source target spills) :
    state.reachable ↔ ∀ dest, state.mapping.symm dest = none →
      target[dest].can_be_freely_generated ∨ spills.is_spilled target[dest] ∨
        ∃ pos : Fin state.stack.length, state.stack[pos] = target[dest] ∧ state.stack.isDupReachable pos :=
  Iff.rfl

example (state : State source target spills) (inv : state.invariant cursor)
    (hw : state.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    Succeeds (buildBottomUp.loop cursor state) (fun _ => True) ↔ state.reachable :=
  loop_success_iff_reachable_within_width cursor state inv hw

-- A final prefix permits an initial stack larger than the DUP window.
example (initial : State source target spills) (hvalid : initial.Valid)
    (hprocessed : initial.processed cursor)
    (hwidth : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial hvalid = .ok ⟨res, trace⟩) ↔ initial.reachable :=
  buildBottomUp_succeeds_iff_reachable_of_processed initial hvalid hprocessed hwidth

example (initial : State source target spills) (hvalid : initial.Valid)
    (hprocessed : initial.processed cursor)
    (hwidth : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ trace : Trace spills source target,
      buildBottomUp initial hvalid = .ok ⟨target, trace⟩) ↔ initial.reachable :=
  buildBottomUp_correct_iff_reachable_of_processed initial hvalid hprocessed hwidth hmapped

example (initial : State source target spills) (hvalid : initial.Valid)
    (hrun : buildBottomUp initial hvalid = .ok result) : initial.reachable :=
  buildBottomUp_reachable_of_ok initial hvalid hrun

example (initial : State source target spills) (hvalid : initial.Valid)
    (hcondition : ∃ cursor, initial.processed cursor ∧ initial.withinReach cursor) :
    ∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial hvalid = .ok ⟨res, trace⟩ := by
  obtain ⟨cursor, hp, hr⟩ := hcondition
  exact buildBottomUp_succeeds_of_processed initial hvalid hp hr

namespace BuildBottomUpReachabilityTests

private def retained (n extra : ℕ) : Mapping n (n + extra) where
  toFun := fun i => some ⟨i.val, by omega⟩
  invFun := fun j => if h : j.val < n then some ⟨j.val, h⟩ else none
  inv a b := by
    have := a.isLt
    split_ifs with h <;> simp_all [Fin.ext_iff, eq_comm]
    omega

private def finalPrefix (stack : Stack) : State stack (stack ++ [.Var ⟨37⟩]) ∅ where
  planned_mapping := ⊥
  stack := stack
  trace := .Lit _
  mapping := by simpa using retained stack.length 1
  pending_generations := 1

private def shallow : Stack := List.replicate 32 (.Lit 0) ++ [.Var ⟨37⟩]
private def buried : Stack := [.Var ⟨37⟩] ++ List.replicate 32 (.Lit 0)

private theorem shallow_valid : (finalPrefix shallow).Valid := ⟨by decide, by decide, by decide⟩

-- A 33-slot final prefix succeeds when the requested variable is at the top.
example : ∃ trace : Trace ∅ shallow (shallow ++ [.Var ⟨37⟩]),
    buildBottomUp (finalPrefix shallow) shallow_valid = .ok ⟨_, trace⟩ := by
  apply buildBottomUp_correct_of_processed (cursor := 33) (finalPrefix shallow) shallow_valid
  · unfold State.processed
    decide
  · constructor
    · decide
    · unfold State.reachable State.isReachable Stack.hasCopy
      decide
  · decide

example : (buildBottomUp (finalPrefix shallow) shallow_valid).map (fun result => result.1) =
    .ok (shallow ++ [.Var ⟨37⟩]) := by native_decide

-- A final prefix alone does not make a buried variable available to DUP.
private theorem buried_valid : (finalPrefix buried).Valid := ⟨by decide, by decide, by decide⟩
example : State.processed 33 (finalPrefix buried) := by unfold State.processed; decide
example : (finalPrefix buried).stack.length - 33 ≤ MAX_SWAP_DEPTH := by decide
example : ¬State.reachable (finalPrefix buried) := by
  unfold State.reachable State.isReachable Stack.hasCopy
  decide
example : (buildBottomUp (finalPrefix buried) buried_valid).map (fun result => result.1) =
    .error (.blocked 17) := by native_decide

example : ¬∃ (res : Stack) (trace : Trace ∅ buried res),
    buildBottomUp (finalPrefix buried) buried_valid = .ok ⟨res, trace⟩ := by
  rw [buildBottomUp_succeeds_iff_reachable_of_processed (cursor := 33)
    (finalPrefix buried) buried_valid
    (by unfold State.processed; decide) (by decide)]
  unfold State.reachable State.isReachable Stack.hasCopy
  decide

private def swapSource : Stack := [.Lit 1] ++ List.replicate 15 (.Lit 0) ++ [.Lit 2]
private def swapTarget : Stack := [.Lit 2] ++ List.replicate 15 (.Lit 0) ++ [.Lit 1]
private def swapState : State swapSource swapTarget ∅ where
  planned_mapping := ⊥
  stack := swapSource
  trace := .Lit _
  mapping := by simpa [swapSource, swapTarget] using (retained 17 0).swapDestinations 0 16
  pending_generations := 0

-- SWAP16 can succeed with 17 active slots and no final bottom prefix.
private theorem swapState_valid : swapState.Valid := ⟨by decide, by decide, by decide⟩
example : (buildBottomUp swapState swapState_valid).map (fun result => result.1) =
    .ok swapTarget := by native_decide
example : ¬∃ cursor, swapState.processed cursor ∧ swapState.withinReach cursor := by
  rintro ⟨cursor, hp, hr⟩
  have hw : 17 - cursor ≤ 16 := hr.width
  have hc : 0 < cursor := by omega
  have hf := hp ⟨0, by decide⟩ hc
  exact (by decide : ¬ ∃ h, swapState.isFinal ⟨0, h⟩) hf

end BuildBottomUpReachabilityTests
