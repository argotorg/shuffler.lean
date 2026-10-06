import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildBottomUp.Lemmas.LoopProofs
import Shuffler.BuildBottomUp.Lemmas.NecessityProofs
import Shuffler.BuildBottomUp.Lemmas.StaticProof
import Shuffler.BuildBottomUp.Lemmas.StaticDecision
import Batteries.Tactic.PrintOpaques

namespace Shuffler.BuildBottomUp

-- Success preserves bound values and generates each unbound target value.
theorem buildBottomUp_expected_of_ok (initial : State source target spills)
    (h : initial.Valid) {res : Stack} {trace : Trace spills source res}
    (hrun : buildBottomUp initial = .ok ⟨res, trace⟩) :
    res = initial.expectedStack := by
  have hs := buildBottomUp_spec initial h
  simpa [hrun, Spec] using hs

theorem buildBottomUp_correct_of_ok (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j])
    {res : Stack} {trace : Trace spills source res}
    (hrun : buildBottomUp initial = .ok ⟨res, trace⟩) : res = target :=
  (buildBottomUp_expected_of_ok initial h hrun).trans (expectedStack_eq_target initial hmapped)

-- The complete condition uses only fixed data from the initial state.
-- There is no bound on the source, current stack, or target length.
theorem buildBottomUp_succeeds_iff_static (initial : State source target spills)
    (h : initial.Valid) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial = .ok ⟨res, trace⟩) ↔ StaticSuccess initial := by
  constructor
  · rintro ⟨res, trace, hrun⟩
    exact (buildBottomUp_static_success_iff initial h).mp ⟨⟨res, trace⟩, hrun, trivial⟩
  · intro hs
    obtain ⟨⟨res, trace⟩, hrun, _⟩ := (buildBottomUp_static_success_iff initial h).mpr hs
    exact ⟨res, trace, hrun⟩

theorem buildBottomUp_correct_iff_static (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ trace : Trace spills source target,
      buildBottomUp initial = .ok ⟨target, trace⟩) ↔ StaticSuccess initial := by
  constructor
  · rintro ⟨trace, hrun⟩
    exact (buildBottomUp_succeeds_iff_static initial h).mp ⟨target, trace, hrun⟩
  · intro hs
    obtain ⟨res, trace, hrun⟩ := (buildBottomUp_succeeds_iff_static initial h).mpr hs
    obtain rfl := buildBottomUp_correct_of_ok initial h hmapped hrun
    exact ⟨trace, hrun⟩

-- Every unbound value must already be within DUP reach or be generatable or loadable.
theorem buildBottomUp_reachable_of_ok (initial : State source target spills)
    (h : initial.Valid) {result} (hrun : buildBottomUp initial = .ok result) :
    Reachable initial := by
  have hs : Success (buildBottomUp initial) (fun _ => True) := ⟨result, hrun, trivial⟩
  unfold buildBottomUp at hs
  rw [StateT.run'_eq] at hs
  exact loop_success_requires_reachable 0 initial (Invariant.initial h) hs.bind_left

-- A final bottom prefix leaves only the reachable part of the stack to process.
theorem buildBottomUp_succeeds_of_processed (initial : State source target spills)
    (h : initial.Valid) (hp : Processed cursor initial) (hr : WithinReach cursor initial) :
    ∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial = .ok ⟨res, trace⟩ := by
  obtain ⟨⟨res, trace⟩, heq, _⟩ := buildBottomUp_success_of_processed initial h hp hr
  exact ⟨res, trace, heq⟩

theorem buildBottomUp_correct_of_processed (initial : State source target spills)
    (h : initial.Valid) (hp : Processed cursor initial) (hr : WithinReach cursor initial)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target, buildBottomUp initial = .ok ⟨target, trace⟩ := by
  obtain ⟨res, trace, heq⟩ := buildBottomUp_succeeds_of_processed initial h hp hr
  obtain rfl := buildBottomUp_correct_of_ok initial h hmapped heq
  exact ⟨trace, heq⟩

-- For at most sixteen remaining stack slots, reachability is also sufficient.
-- The initial stack and the target can be arbitrarily long.
theorem buildBottomUp_succeeds_iff_reachable_of_processed
    (initial : State source target spills) (h : initial.Valid)
    (hp : Processed cursor initial) (hw : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial = .ok ⟨res, trace⟩) ↔ Reachable initial := by
  constructor
  · rintro ⟨res, trace, hrun⟩
    exact buildBottomUp_reachable_of_ok initial h hrun
  · intro hr
    exact buildBottomUp_succeeds_of_processed initial h hp ⟨hw, hr⟩

theorem buildBottomUp_correct_iff_reachable_of_processed
    (initial : State source target spills) (h : initial.Valid)
    (hp : Processed cursor initial) (hw : initial.stack.length - cursor ≤ MAX_SWAP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ trace : Trace spills source target,
      buildBottomUp initial = .ok ⟨target, trace⟩) ↔ Reachable initial := by
  constructor
  · rintro ⟨trace, hrun⟩
    exact buildBottomUp_reachable_of_ok initial h hrun
  · intro hr
    exact buildBottomUp_correct_of_processed initial h hp ⟨hw, hr⟩ hmapped

-- DUP depths start at zero, so sixteen initial slots fit within reach.
-- The target length is unrestricted.
theorem buildBottomUp_succeeds_small (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    ∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial = .ok ⟨res, trace⟩ := by
  obtain ⟨⟨res, trace⟩, heq, _⟩ := buildBottomUp_success initial h hsmall
  exact ⟨res, trace, heq⟩

theorem buildBottomUp_correct_within_dup_reach (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target, buildBottomUp initial = .ok ⟨target, trace⟩ := by
  obtain ⟨res, trace, heq⟩ := buildBottomUp_succeeds_small initial h hsmall
  obtain rfl := buildBottomUp_correct_of_ok initial h hmapped heq
  exact ⟨trace, heq⟩

theorem buildBottomUp_correct_small (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length < MAX_DUP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target, buildBottomUp initial = .ok ⟨target, trace⟩ :=
  buildBottomUp_correct_within_dup_reach initial h (by omega) hmapped

-- Valid states have the required size, pending count, and available target values.
-- Operations outside DUP or SWAP reach can still return a blocked error.
theorem buildBottomUp_no_assertion (initial : State source target spills)
    (h : initial.Valid) (reason : String) :
    buildBottomUp initial ≠ .error (.assertion reason) :=
  (buildBottomUp_spec initial h).noAssertion reason

theorem buildBottomUp_error_is_blocked (initial : State source target spills)
    (h : initial.Valid) (he : buildBottomUp initial = .error err) :
    ∃ excess, err = .blocked excess :=
  (buildBottomUp_spec initial h).error he

-- Audit the whole function, including the recursion and the action helpers.
/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_no_assertion

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_of_ok

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_small

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_within_dup_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_within_dup_reach

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_reachable_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_reachable_of_ok

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_succeeds_iff_reachable_of_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_succeeds_iff_reachable_of_processed

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_iff_reachable_of_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_iff_reachable_of_processed

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_succeeds_iff_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_succeeds_iff_static

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_iff_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_iff_static

end Shuffler.BuildBottomUp
