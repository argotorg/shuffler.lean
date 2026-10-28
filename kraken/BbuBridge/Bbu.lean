import BbuBridge.Push
import BbuBridge.Dup
import BbuBridge.SwapWith
import BbuBridge.SwapDest
import BbuBridge.Produce
import BbuBridge.Generate
import BbuBridge.Urgent
import BbuBridge.CopyScan
import BbuBridge.Finish
import BbuBridge.RestUrgent
import BbuBridge.RestTop
import BbuBridge.RestBound
import BbuBridge.RestUnbound
import BbuBridge.Step
import BbuBridge.Loop
import BbuBridge.Init
import BbuBridge.InitValid
import BbuBridge.Expected

/-!
The model `Bbu.buildBottomUp` is the original `buildBottomUp` on the decoded
inputs (`buildBottomUp_eq`), and so the theorems about the original hold for the
model.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

theorem generate_corr' : GenerateStmt :=
  generate_corr (produce_corr push_corr dup_corr) swapWith_corr swapDest_corr

theorem loop_corr' : LoopStmt :=
  loop_corr
    (step_corr urgent_corr (restUrgent_corr generate_corr') (restTop_corr generate_corr')
      (restBound_corr copyScan_corr swapDest_corr swapWith_corr)
      (restUnbound_corr generate_corr' swapWith_corr))
    finish_corr

variable {e : Bbu.Env} {source : List Bbu.Word} {dests : List Nat}

-- The model is the original on the decoded inputs: the same operations, or the
-- same error.
theorem buildBottomUp_eq (h : ModelValid e source dests) :
    Bbu.buildBottomUp e source dests =
      encodeRes (buildBottomUp (initState e source dests h) (initValid e source dests h)) := by
  rw [buildBottomUp_eq_post]
  exact loop_corr' e _ _ _ 0 (initRel e source dests h)

-- The model does not fail an assertion.
theorem model_no_assertion (h : ModelValid e source dests) :
    Bbu.buildBottomUp e source dests ≠ .error .assertion := by
  rw [buildBottomUp_eq h]
  cases hr : buildBottomUp (initState e source dests h) (initValid e source dests h) with
  | ok r => simp [encodeRes, encodeM]
  | error err =>
    cases err with
    | Blocked b => simp [encodeRes, encodeM, encodeErr]
    | assertion reason => exact absurd hr (buildBottomUp_no_assertion _ _ reason)

-- The model operations are a trace from the source to the expected stack.
theorem model_ok (h : ModelValid e source dests) {ops : List Bbu.Op}
    (hok : Bbu.buildBottomUp e source dests = .ok ops) :
    ∃ trace : Trace (spillSet e) (source.map decode) ((expected e source dests).map decode),
      (traceOps trace).map encodeOp = ops := by
  rw [buildBottomUp_eq h] at hok
  cases hr : buildBottomUp (initState e source dests h) (initValid e source dests h) with
  | error err =>
    rw [hr] at hok
    cases hok
  | ok r =>
    obtain ⟨res, trace⟩ := r
    rw [hr] at hok
    have hres := buildBottomUp_expected_of_ok _ _ hr
    rw [expected_eq e source dests h] at hres
    subst hres
    exact ⟨trace, by simpa [encodeRes, encodeM] using hok⟩

-- If the destinations connect equal values, the model operations are a trace
-- from the source to the target.
theorem model_ok_target (h : ModelValid e source dests) (hm : Mapped e source dests)
    {ops : List Bbu.Op} (hok : Bbu.buildBottomUp e source dests = .ok ops) :
    ∃ trace : Trace (spillSet e) (source.map decode) (tgt e), (traceOps trace).map encodeOp = ops := by
  rw [buildBottomUp_eq h] at hok
  cases hr : buildBottomUp (initState e source dests h) (initValid e source dests h) with
  | error err =>
    rw [hr] at hok
    cases hok
  | ok r =>
    obtain ⟨res, trace⟩ := r
    rw [hr] at hok
    have hres := buildBottomUp_correct_of_ok _ _ (mapped e source dests h hm) hr
    subst hres
    exact ⟨trace, by simpa [encodeRes, encodeM] using hok⟩

-- The model succeeds if and only if the static success condition holds.
theorem model_ok_iff_static (h : ModelValid e source dests) :
    (∃ ops, Bbu.buildBottomUp e source dests = .ok ops) ↔
      StaticSuccess (initState e source dests h) := by
  rw [← buildBottomUp_succeeds_iff_static _ (initValid e source dests h), buildBottomUp_eq h]
  cases hr : buildBottomUp (initState e source dests h) (initValid e source dests h) with
  | error err => simp [encodeRes, encodeM]
  | ok r => exact iff_of_true ⟨_, rfl⟩ ⟨r.1, r.2, rfl⟩

-- The model succeeds for a source of at most 16 values.
theorem model_ok_small (h : ModelValid e source dests) (hs : source.length ≤ 16) :
    ∃ ops, Bbu.buildBottomUp e source dests = .ok ops := by
  obtain ⟨res, trace, hr⟩ :=
    buildBottomUp_succeeds_small _ (initValid e source dests h) (by simpa [initState, MAX_DUP_DEPTH] using hs)
  rw [buildBottomUp_eq h, hr]
  exact ⟨_, rfl⟩

end BbuBridge
