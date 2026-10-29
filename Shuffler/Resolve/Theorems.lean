import Shuffler.Resolve.Lemmas
import Shuffler.Resolve.Lemmas.Preservation
import Shuffler.Resolve.Lemmas.Progress
import Batteries.Tactic.PrintOpaques

open Std.Do

namespace Shuffler.Planner

variable {source target : Stack}

-- Every call returns a success flag and a state, including calls that cannot drop enough slots.
theorem resolve_ok (init : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) :
    ∃ result, resolve init mapping blocked current = .ok result := by
  have h := resolve_success_triple init mapping blocked current
  apply Except.of_wp_eq rfl (fun result => ∃ value, result = .ok value)
  simpa [PostCond.noThrow, Triple, ExceptConds.false, ExceptConds.const] using h

-- Each required target value remains available, including after an attempt that returns false.
theorem resolve_preserves_target_available (init result : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) (success : Bool)
    (havailable : init.TargetAvailable) (hretained : init.RetainedUndropped mapping)
    (hresolve : resolve init mapping blocked current = .ok (success, result)) :
    result.TargetAvailable := by
  have hs := resolve_targetAvailable_triple init mapping blocked current
  change init.TargetAvailable ∧ init.RetainedUndropped mapping → _ at hs
  have hr := hs ⟨havailable, hretained⟩
  rw [hresolve] at hr
  exact hr

-- A successful call drops exactly the requested number of additional source positions.
-- Retained positions must be undropped when the call starts.
theorem resolve_droppedCount_of_success (initial result : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length)
    (hretained : initial.RetainedUndropped mapping)
    (hresolve : resolve initial mapping blocked current = .ok (true, result)) :
    result.droppedCount = initial.droppedCount + blocked.excess := by
  have h := resolve_progress_triple initial mapping blocked current
  rw [hresolve] at h
  exact h hretained rfl

-- Positive excess gives strict progress on each successful call.
theorem resolve_droppedCount_strict (initial result : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length)
    (hretained : initial.RetainedUndropped mapping)
    (hresolve : resolve initial mapping blocked current = .ok (true, result))
    (hexcess : 0 < blocked.excess) : initial.droppedCount < result.droppedCount := by
  rw [resolve_droppedCount_of_success initial result mapping blocked current hretained hresolve]
  omega

-- The number of source positions not dropped is a decreasing measure for successful retries.
theorem resolve_remaining_strict (initial result : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length)
    (hretained : initial.RetainedUndropped mapping)
    (hresolve : resolve initial mapping blocked current = .ok (true, result))
    (hexcess : 0 < blocked.excess) :
    source.length - result.droppedCount < source.length - initial.droppedCount := by
  have := resolve_droppedCount_strict initial result mapping blocked current hretained hresolve hexcess
  have := result.droppedCount_le
  omega

-- Audit the production function and the complete proofs, including all loop lemmas.
/-- info: 'Shuffler.Planner.resolve' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques resolve

/-- info: 'Shuffler.Planner.resolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolve

/-- info: 'Shuffler.Planner.resolve_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolve_ok

/-- info: 'Shuffler.Planner.resolve_preserves_target_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolve_preserves_target_available

/-- info: 'Shuffler.Planner.resolve_droppedCount_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolve_droppedCount_of_success

/-- info: 'Shuffler.Planner.resolve_remaining_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolve_remaining_strict

end Shuffler.Planner
