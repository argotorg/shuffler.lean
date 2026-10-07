import Shuffler.Optimality.SwapRuns
import Shuffler.Optimality.ValueGraph.CertifiedComplete

namespace Shuffler.Optimality.SwapRuns

open Shuffler.Placement

theorem improve_min_swaps (run : BuiltTrace spills source target 0)
    (other : Trace spills source target) (heligible : Eligible 0 other) :
    (improve run).trace.swapCount ≤ other.swapCount := by
  by_cases hz : run.trace.swapCount = 0
  · simp only [improve, hz, ↓reduceIte]
    exact Nat.zero_le _
  · have hr : Reserve spills source target 0 :=
      CanPlace.reserve ⟨run.trace, run.noPop, run.additions⟩
    obtain ⟨built, hb⟩ := Option.isSome_iff_exists.mp
      (ValueGraph.build_complete spills source target hr)
    simp only [improve, hz, ↓reduceIte, hb, Option.getD_some]
    exact ValueGraph.build_min_swaps spills source target built hb other heligible

theorem improve_cost_le (costs : PrimitiveCosts) (run : BuiltTrace spills source target 0) :
    (traceCost costs (improve run).trace).AtMost (traceCost costs run.trace) := by
  have hs := improve_min_swaps run run.trace ⟨run.noPop, run.additions⟩
  have hw : ∀ weights : Weights,
      (traceCost costs (improve run).trace).score weights ≤
        (traceCost costs run.trace).score weights := by
    intro weights
    rw [noGrowth_score costs weights _ (improve run).noPop (improve run).additions,
      noGrowth_score costs weights _ run.noPop run.additions]
    exact Nat.mul_le_mul_right _ hs
  exact ⟨by simpa using hw .gasOnly, by simpa using hw .bytesOnly⟩

theorem withoutSwaps_concat (first : Trace spills source middle)
    (second : Trace spills middle target) :
    withoutSwaps (first.concat second) = withoutSwaps first ++ withoutSwaps second := by
  induction second <;> simp_all [Trace.concat, withoutSwaps, List.append_assoc]

theorem withoutSwaps_of_noGrowth (trace : Trace spills source target)
    (hpop : trace.noPop) (hadd : trace.additions = 0) : withoutSwaps trace = [] := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih => exact ih hpop hadd
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_zero] at hc
      omega
  | Pop _ trace ih => exact False.elim hpop

private theorem noPop_concat_iff (first : Trace spills source middle)
    (second : Trace spills middle target) (hsecond : second.noPop) :
    (first.concat second).noPop ↔ first.noPop := by
  induction second with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      exact ih hsecond
  | Pop _ trace ih => exact False.elim hsecond

theorem Pending.flush_noPop (pending : Pending spills source target) :
    pending.flush.noPop ↔ pending.before.noPop :=
  noPop_concat_iff pending.before _ (improve pending.run).noPop

theorem Pending.raw_noPop (pending : Pending spills source target) :
    pending.raw.noPop ↔ pending.before.noPop :=
  noPop_concat_iff pending.before _ pending.run.noPop

theorem Pending.flush_additions (pending : Pending spills source target) :
    pending.flush.additions = pending.before.additions := by
  simp only [Pending.flush, Trace.additions_concat, (improve pending.run).additions, add_zero]

theorem Pending.raw_additions (pending : Pending spills source target) :
    pending.raw.additions = pending.before.additions := by
  simp only [Pending.raw, Trace.additions_concat, pending.run.additions, add_zero]

theorem Pending.flush_withoutSwaps (pending : Pending spills source target) :
    withoutSwaps pending.flush = withoutSwaps pending.before := by
  rw [Pending.flush, withoutSwaps_concat,
    withoutSwaps_of_noGrowth _ (improve pending.run).noPop (improve pending.run).additions,
    List.append_nil]

theorem Pending.flush_cost_le (costs : PrimitiveCosts) (pending : Pending spills source target) :
    (traceCost costs pending.flush).AtMost (traceCost costs pending.raw) := by
  have hh := improve_cost_le costs pending.run
  simp only [Pending.flush, Pending.raw, traceCost_concat, Cost.AtMost, Cost.add] at hh ⊢
  exact ⟨Nat.add_le_add_left hh.1 _, Nat.add_le_add_left hh.2 _⟩

theorem scan_noPop (trace : Trace spills source target) :
    (scan trace).before.noPop ↔ trace.noPop := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih => exact ih
  | Pop _ trace ih => rfl
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      exact (Pending.flush_noPop (scan trace)).trans ih

theorem scan_additions (trace : Trace spills source target) :
    (scan trace).before.additions = trace.additions := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih => exact ih
  | Dup _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [scan]
      simp only [Pending.ofTrace, Trace.additions, Pending.flush_additions, ih]

theorem scan_withoutSwaps (trace : Trace spills source target) :
    withoutSwaps (scan trace).before = withoutSwaps trace := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih => exact ih
  | Dup _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [scan]
      simp only [Pending.ofTrace, withoutSwaps, Pending.flush_withoutSwaps, ih]

theorem scan_cost_le (costs : PrimitiveCosts) (trace : Trace spills source target) :
    (traceCost costs (scan trace).raw).AtMost (traceCost costs trace) := by
  induction trace with
  | Lit => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | Swap depth hlen hlo hhi trace ih =>
      rw [scan]
      simpa only [Pending.appendSwap, Pending.raw, Trace.concat, traceCost, Cost.AtMost, Cost.add] using
        And.intro (Nat.add_le_add_right ih.1 costs.swap.gas)
          (Nat.add_le_add_right ih.2 costs.swap.bytes)
  | Dup depth hlen hlo hhi trace ih | Pop hlen trace ih | Push value hfree trace ih
    | Load id hspill trace ih =>
      have hf := Pending.flush_cost_le costs (scan trace)
      have hh : (traceCost costs (scan trace).flush).AtMost (traceCost costs trace) :=
        ⟨hf.1.trans ih.1, hf.2.trans ih.2⟩
      rw [scan]
      simp only [Pending.raw, Pending.ofTrace, Trace.concat, traceCost, Cost.AtMost,
        Cost.add] at hh ⊢
      exact ⟨Nat.add_le_add_right hh.1 _, Nat.add_le_add_right hh.2 _⟩

theorem normalize_noPop (trace : Trace spills source target) :
    (normalize trace).noPop ↔ trace.noPop := by
  rw [normalize, Pending.flush_noPop, scan_noPop]

theorem normalize_additions (trace : Trace spills source target) :
    (normalize trace).additions = trace.additions := by
  rw [normalize, Pending.flush_additions, scan_additions]

-- Every non-SWAP instruction keeps its value, depth, and execution order.
theorem normalize_withoutSwaps (trace : Trace spills source target) :
    withoutSwaps (normalize trace) = withoutSwaps trace := by
  rw [normalize, Pending.flush_withoutSwaps, scan_withoutSwaps]

-- Each component decreases for every supplied primitive cost model.
theorem normalize_cost_le (costs : PrimitiveCosts) (trace : Trace spills source target) :
    (traceCost costs (normalize trace)).AtMost (traceCost costs trace) := by
  have hf := Pending.flush_cost_le costs (scan trace)
  have hs := scan_cost_le costs trace
  exact ⟨hf.1.trans hs.1, hf.2.trans hs.2⟩

theorem normalize_score_le (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    (traceCost costs (normalize trace)).score weights ≤ (traceCost costs trace).score weights :=
  Cost.score_le_of_atMost weights (normalize_cost_le costs trace)

theorem births_concat (first : Trace spills source middle) (second : Trace spills middle target) :
    births (first.concat second) = births first ++ births second := by
  induction second <;> simp_all [Trace.concat, births, List.append_assoc]

theorem births_of_noGrowth (trace : Trace spills source target)
    (hpop : trace.noPop) (hadd : trace.additions = 0) : births trace = [] := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih => exact ih hpop hadd
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_zero] at hc
      omega
  | Pop _ trace ih => exact False.elim hpop

theorem Pending.flush_births (pending : Pending spills source target) :
    births pending.flush = births pending.before := by
  rw [Pending.flush, births_concat,
    births_of_noGrowth _ (improve pending.run).noPop (improve pending.run).additions,
    List.append_nil]

theorem scan_births (trace : Trace spills source target) :
    births (scan trace).before = births trace := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih => exact ih
  | Dup _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [scan]
      simp only [Pending.ofTrace, births, Pending.flush_births, ih]

theorem normalize_births (trace : Trace spills source target) :
    births (normalize trace) = births trace := by
  rw [normalize, Pending.flush_births, scan_births]

theorem scan_of_noGrowth (trace : Trace spills source target)
    (hpop : trace.noPop) (hadd : trace.additions = 0) :
    scan trace = ⟨source, .Lit source, ⟨trace, hpop, hadd⟩⟩ := by
  induction trace with
  | Lit => rfl
  | Swap depth hlen hlo hhi trace ih =>
      change (scan trace).appendSwap depth hlen hlo hhi = _
      rw [ih hpop hadd]
      rfl
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      have hc := congrArg Multiset.card hadd
      simp only [Trace.additions, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_zero] at hc
      omega
  | Pop _ trace ih => exact False.elim hpop

private theorem lit_concat (trace : Trace spills source target) :
    (Trace.Lit source).concat trace = trace := by
  induction trace <;> simp_all only [Trace.concat]

-- If the whole input is one SWAP run, the output has the global minimum
-- SWAP count for these exact endpoints, including repeated values.
theorem normalize_noGrowth_min_swaps (trace other : Trace spills source target)
    (htrace : Eligible 0 trace) (hother : Eligible 0 other) :
    (normalize trace).swapCount ≤ other.swapCount := by
  rw [normalize, scan_of_noGrowth trace htrace.1 htrace.2]
  simp only [Pending.flush, lit_concat]
  exact improve_min_swaps ⟨trace, htrace.1, htrace.2⟩ other hother

def normalizeBuilt (built : BuiltTrace spills source target missing) :
    BuiltTrace spills source target missing :=
  ⟨normalize built.trace, (normalize_noPop built.trace).mpr built.noPop,
    (normalize_additions built.trace).trans built.additions⟩

end Shuffler.Optimality.SwapRuns
