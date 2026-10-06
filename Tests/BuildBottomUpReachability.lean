import Shuffler

open Shuffler.BuildBottomUp

set_option maxRecDepth 16384

example (state : State source target spills) (inv : Invariant cursor state)
    (hw : state.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) ↔ Reachable state :=
  loop_success_iff_reachable_within_width cursor state inv hw

-- A final prefix permits an initial stack larger than the DUP window.
example (initial : State source target spills) (hvalid : initial.Valid)
    (hprocessed : Processed cursor initial)
    (hwidth : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial = .ok ⟨res, trace⟩) ↔ Reachable initial :=
  buildBottomUp_succeeds_iff_reachable_of_processed initial hvalid hprocessed hwidth

example (initial : State source target spills) (hvalid : initial.Valid)
    (hprocessed : Processed cursor initial)
    (hwidth : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ trace : Trace spills source target,
      buildBottomUp initial = .ok ⟨target, trace⟩) ↔ Reachable initial :=
  buildBottomUp_correct_iff_reachable_of_processed initial hvalid hprocessed hwidth hmapped

example (initial : State source target spills) (hvalid : initial.Valid)
    (hrun : buildBottomUp initial = .ok result) : Reachable initial :=
  buildBottomUp_reachable_of_ok initial hvalid hrun

example (initial : State source target spills) (hvalid : initial.Valid)
    (hcondition : ∃ cursor, Processed cursor initial ∧ WithinReach cursor initial) :
    ∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial = .ok ⟨res, trace⟩ := by
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

-- A 33-slot final prefix succeeds when the requested variable is at the top.
example : ∃ trace : Trace ∅ shallow (shallow ++ [.Var ⟨37⟩]),
    buildBottomUp (finalPrefix shallow) = .ok ⟨_, trace⟩ := by
  apply buildBottomUp_correct_of_processed (cursor := 33) (finalPrefix shallow)
  · exact ⟨by decide, by decide, by decide⟩
  · unfold Processed
    decide
  · constructor
    · decide
    · unfold Reachable HasCopy
      decide
  · decide

example : (buildBottomUp (finalPrefix shallow)).map (fun result => result.1) =
    .ok (shallow ++ [.Var ⟨37⟩]) := by native_decide

-- A final prefix alone does not make a buried variable available to DUP.
example : (finalPrefix buried).Valid := ⟨by decide, by decide, by decide⟩
example : Processed 33 (finalPrefix buried) := by unfold Processed; decide
example : (finalPrefix buried).stack.length - 33 ≤ MAX_SWAP_DEPTH := by decide
example : ¬Reachable (finalPrefix buried) := by
  unfold Reachable HasCopy
  decide
example : (buildBottomUp (finalPrefix buried)).map (fun result => result.1) =
    .error (.blocked 17) := by native_decide

example : ¬∃ (res : Stack) (trace : Trace ∅ buried res),
    buildBottomUp (finalPrefix buried) = .ok ⟨res, trace⟩ := by
  rw [buildBottomUp_succeeds_iff_reachable_of_processed (cursor := 33)
    (finalPrefix buried) ⟨by decide, by decide, by decide⟩
    (by unfold Processed; decide) (by decide)]
  unfold Reachable HasCopy
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
example : swapState.Valid := ⟨by decide, by decide, by decide⟩
example : (buildBottomUp swapState).map (fun result => result.1) = .ok swapTarget := by
  native_decide
example : ¬∃ cursor, Processed cursor swapState ∧ WithinReach cursor swapState := by
  rintro ⟨cursor, hp, hr⟩
  have hw : 17 - cursor ≤ 16 := hr.width
  have hc : 0 < cursor := by omega
  have hf := hp ⟨0, by decide⟩ hc
  exact (by decide : ¬swapState.isFinal 0) hf

end BuildBottomUpReachabilityTests
