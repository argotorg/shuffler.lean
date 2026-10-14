import Shuffler.BuildBottomUp.Theorems.Correctness
import Shuffler.BuildBottomUp.Lemmas.NecessityProofs

namespace Shuffler.BuildBottomUp

-- Success requires that each unbound target value can be freely generated, is spilled, or has a
-- copy in DUP reach of the initial stack.
theorem buildBottomUp_reachable_of_ok (initial : State source target spills)
    (h : initial.Valid) {result} (hrun : buildBottomUp initial h = .ok result) :
    initial.reachable := by
  have hs : Succeeds (buildBottomUp initial h) (fun _ => True) := ⟨result, hrun, trivial⟩
  exact loop_success_requires_reachable 0 initial (State.invariant.initial h)
    ((buildBottomUp_success_iff_loop initial h).mp hs)

-- buildBottomUp succeeds if a bottom prefix is already final, at most 16 slots are above it, and
-- each unbound target value can be generated, loaded, or DUPed.
theorem buildBottomUp_succeeds_of_processed (initial : State source target spills)
    (h : initial.Valid) (hp : initial.processed cursor) (hr : initial.withinReach cursor) :
    ∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial h = .ok ⟨res, trace⟩ := by
  obtain ⟨⟨res, trace⟩, heq, _⟩ := buildBottomUp_success_of_processed initial h hp hr
  exact ⟨res, trace, heq⟩

-- Under the same conditions, if the mapping connects only slots of equal value, buildBottomUp
-- returns the target.
theorem buildBottomUp_correct_of_processed (initial : State source target spills)
    (h : initial.Valid) (hp : initial.processed cursor) (hr : initial.withinReach cursor)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target, buildBottomUp initial h = .ok ⟨target, trace⟩ := by
  obtain ⟨res, trace, heq⟩ := buildBottomUp_succeeds_of_processed initial h hp hr
  obtain rfl := buildBottomUp_correct_of_ok initial h hmapped heq
  exact ⟨trace, heq⟩

-- If a bottom prefix is already final and at most 16 slots are above it, buildBottomUp succeeds
-- if and only if each unbound target value can be generated, loaded, or DUPed.
theorem buildBottomUp_succeeds_iff_reachable_of_processed
    (initial : State source target spills) (h : initial.Valid)
    (hp : initial.processed cursor) (hw : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial h = .ok ⟨res, trace⟩) ↔ initial.reachable := by
  constructor
  · rintro ⟨res, trace, hrun⟩
    exact buildBottomUp_reachable_of_ok initial h hrun
  · intro hr
    exact buildBottomUp_succeeds_of_processed initial h hp ⟨hw, hr⟩

-- The same equivalence for a result equal to the target, if the mapping connects only slots of
-- equal value.
theorem buildBottomUp_correct_iff_reachable_of_processed
    (initial : State source target spills) (h : initial.Valid)
    (hp : initial.processed cursor) (hw : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ trace : Trace spills source target,
      buildBottomUp initial h = .ok ⟨target, trace⟩) ↔ initial.reachable := by
  constructor
  · rintro ⟨trace, hrun⟩
    exact buildBottomUp_reachable_of_ok initial h hrun
  · intro hr
    exact buildBottomUp_correct_of_processed initial h hp ⟨hw, hr⟩ hmapped

end Shuffler.BuildBottomUp
