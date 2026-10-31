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

variable {e : Bbu.Env} {source : List Bbu.StackSlot} {dests : List Nat}

-- The model is the original on the decoded inputs: both are done or both are
-- blocked at the same slot by the same excess, with the same stack,
-- destinations, pending count and operations; or both fail an assertion.
theorem buildBottomUp_eq (h : ModelValid e source dests) :
    ResCorr (Rel e) (Bbu.buildBottomUp e source dests)
      (buildBottomUp (initState e source dests h) (initValid e source dests h)) := by
  rw [buildBottomUp_eq_post]
  exact loop_corr' e _ _ _ 0 (initRel e source dests h)

-- Canonical slots are equal if their values are equal.
theorem map_decode_inj {a b : List Bbu.StackSlot} (ha : ∀ v ∈ a, Canon v) (hb : ∀ v ∈ b, Canon v)
    (h : a.map decode = b.map decode) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases b with
    | nil => cases h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at ha hb
      rw [decode_inj ha.1 hb.1 h.1, ih ha.2 hb.2 h.2]

theorem canon_getElem! {l : List Bbu.StackSlot} (hl : ∀ v ∈ l, Canon v) (i : Nat) :
    Canon l[i]! := by
  by_cases hi : i < l.length
  · rw [getElem!_pos l i hi]; exact hl _ (List.getElem_mem hi)
  · rw [getElem!_neg l i hi]; exact canon_default

theorem canon_expected (h : ModelValid e source dests) : ∀ v ∈ expected e source dests, Canon v := by
  intro v hv
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hv
  split
  · exact canon_getElem! h.canonSource _
  · exact canon_getElem! h.canonTarget _

theorem canon_vals {st : Bbu.St} (hc : ∀ s ∈ st.slots, Canon s.val) :
    ∀ v ∈ st.slots.map Bbu.Slot.val, Canon v := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
  exact hc s hs

-- A done model run is a done original run with a related state.
theorem orig_of_ok (h : ModelValid e source dests) {st : Bbu.St}
    (hok : Bbu.buildBottomUp e source dests = .ok st) :
    ∃ r, buildBottomUp (initState e source dests h) (initValid e source dests h) = .ok ⟨none, r⟩ ∧
      Rel e st r := by
  have hc := buildBottomUp_eq h
  rw [hok] at hc
  revert hc
  rcases buildBottomUp (initState e source dests h) (initValid e source dests h) with _ | ⟨_ | b, r⟩
  · exact False.elim
  · exact fun hc => ⟨r, rfl, hc.2⟩
  · rintro ⟨hb, -⟩
    cases hb

-- The model does not fail an assertion.
theorem model_no_assertion (h : ModelValid e source dests) :
    Bbu.buildBottomUp e source dests ≠ .error .assertion := by
  intro hok
  have hc := buildBottomUp_eq h
  rw [hok] at hc
  cases hr : buildBottomUp (initState e source dests h) (initValid e source dests h) with
  | ok r => rw [hr] at hc; exact hc
  | error err =>
    rw [hr] at hc
    cases err with
    | Blocked b => exact hc
    | assertion reason => exact buildBottomUp_no_assertion _ _ reason hr

-- The model builds the expected stack, and its operations are a trace from the
-- source to the expected stack.
theorem model_ok (h : ModelValid e source dests) {st : Bbu.St}
    (hok : Bbu.buildBottomUp e source dests = .ok st) :
    st.slots.map Bbu.Slot.val = expected e source dests ∧
      ∃ trace : Trace (spillSet e (source.map decode)) (source.map decode)
        ((expected e source dests).map decode),
        (traceOps trace).map encodeOp = st.trace := by
  obtain ⟨r, hr, hrel⟩ := orig_of_ok h hok
  have hres := buildBottomUp_expected_of_ok _ _ hr
  rw [expected_eq e source dests h] at hres
  obtain ⟨_, stack, trace, _, _⟩ := r
  simp only at hres
  subst hres
  refine ⟨map_decode_inj (canon_vals hrel.canon) (canon_expected h) ?_, trace, hrel.trace⟩
  rw [List.map_map]
  exact hrel.stack.symm

-- If the destinations connect equal values, the model builds the target, and
-- its operations are a trace from the source to the target.
theorem model_ok_target (h : ModelValid e source dests) (hm : Mapped e source dests)
    {st : Bbu.St} (hok : Bbu.buildBottomUp e source dests = .ok st) :
    st.slots.map Bbu.Slot.val = e.target ∧
      ∃ trace : Trace (spillSet e (source.map decode)) (source.map decode) (tgt e),
        (traceOps trace).map encodeOp = st.trace := by
  obtain ⟨r, hr, hrel⟩ := orig_of_ok h hok
  have hres := buildBottomUp_correct_of_ok _ _ (mapped e source dests h hm) hr
  obtain ⟨_, stack, trace, _, _⟩ := r
  simp only at hres
  subst hres
  refine ⟨map_decode_inj (canon_vals hrel.canon) h.canonTarget ?_, trace, hrel.trace⟩
  rw [List.map_map]
  exact hrel.stack.symm

-- The model is done if and only if the static success condition holds.
theorem model_ok_iff_static (h : ModelValid e source dests) :
    (∃ st, Bbu.buildBottomUp e source dests = .ok st) ↔
      StaticSuccess (initState e source dests h) := by
  rw [← buildBottomUp_succeeds_iff_static _ (initValid e source dests h)]
  constructor
  · rintro ⟨st, hok⟩
    obtain ⟨r, hr, -⟩ := orig_of_ok h hok
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    have hc := buildBottomUp_eq h
    rw [hr] at hc
    revert hc
    rcases Bbu.buildBottomUp e source dests with (⟨pos, ex, a⟩ | _) | st
    · rintro ⟨hb, -⟩
      cases hb
    · exact False.elim
    · exact fun _ => ⟨st, rfl⟩

-- The model is done for a source of at most 16 values.
theorem model_ok_small (h : ModelValid e source dests) (hs : source.length ≤ 16) :
    ∃ st, Bbu.buildBottomUp e source dests = .ok st := by
  obtain ⟨r, hr⟩ :=
    buildBottomUp_succeeds_small _ (initValid e source dests h) (by simpa [initState, MAX_DUP_DEPTH] using hs)
  exact (model_ok_iff_static h).mpr ((buildBottomUp_succeeds_iff_static _ _).mp ⟨r, hr⟩)

end BbuBridge
