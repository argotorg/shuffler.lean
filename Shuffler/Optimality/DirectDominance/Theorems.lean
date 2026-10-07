import Shuffler.Optimality.DirectDominance
import Shuffler.Placement.Build

namespace Shuffler.Optimality.DirectDominance

open Shuffler.Placement

theorem appendDirect_noPop (trace : Trace spills source target) (value : Value)
    (hfree : Free spills value) : (appendDirect trace value hfree).noPop ↔ trace.noPop := by
  cases value <;> try rfl
  simp [Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

theorem appendDirect_additions (trace : Trace spills source target) (value : Value)
    (hfree : Free spills value) :
    (appendDirect trace value hfree).additions = trace.additions + {value} := by
  cases value <;> try rfl
  simp [Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

theorem appendDirect_swapCount (trace : Trace spills source target) (value : Value)
    (hfree : Free spills value) : (appendDirect trace value hfree).swapCount = trace.swapCount := by
  cases value <;> try rfl
  simp [Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

theorem appendDirect_dupCount (trace : Trace spills source target) (value other : Value)
    (hfree : Free spills value) :
    Lineage.dupCount other (appendDirect trace value hfree) = Lineage.dupCount other trace := by
  cases value <;> try rfl
  simp [Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

theorem appendDirect_statePath (trace : Trace spills source target) (value : Value)
    (hfree : Free spills value) :
    statePath (appendDirect trace value hfree) = statePath trace ++ [target ++ [value]] := by
  cases value <;> try rfl
  simp [Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

theorem appendDirect_score (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (value : Value) (hfree : Free spills value) :
    (traceCost costs (appendDirect trace value hfree)).score weights =
      (traceCost costs trace).score weights + directPrice costs weights spills value := by
  cases value with
  | Lit _ | Wildcard => simp [appendDirect, traceCost, Cost.score_add, directPrice]
  | Var id =>
      have hs : id ∈ spills := by
        simpa [Free, Value.can_be_freely_generated, SpillSet.is_spilled] using hfree
      simp [appendDirect, traceCost, Cost.score_add, directPrice, hs]
  | FunctionReturnLabel =>
      simp [Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

theorem normalize_noPop (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    (normalize costs weights trace).noPop ↔ trace.noPop := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [normalize]
      simp only [Trace.noPop, ih]
  | Dup _ _ _ _ trace ih =>
      rw [normalize]
      dsimp only
      split_ifs <;> simp only [appendDirect_noPop, Trace.noPop, ih]

theorem normalize_additions (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    (normalize costs weights trace).additions = trace.additions := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [normalize]
      simp only [Trace.additions, ih]
  | Dup _ _ _ _ trace ih =>
      rw [normalize]
      dsimp only
      split_ifs <;> simp only [appendDirect_additions, Trace.additions, ih]

theorem normalize_swapCount (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    (normalize costs weights trace).swapCount = trace.swapCount := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [normalize]
      simp only [Trace.swapCount, ih]
  | Dup _ _ _ _ trace ih =>
      rw [normalize]
      dsimp only
      split_ifs <;> simp only [appendDirect_swapCount, Trace.swapCount, ih]

-- Each original step and its replacement have the same before and after
-- stacks. The entire sequence of concrete stack states stays the same.
theorem normalize_statePath (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    statePath (normalize costs weights trace) = statePath trace := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [normalize]
      simp only [statePath, ih]
  | Dup _ _ _ _ trace ih =>
      rw [normalize]
      dsimp only
      split_ifs <;> simp only [appendDirect_statePath, statePath, ih]

theorem normalize_score_le (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) :
    (traceCost costs (normalize costs weights trace)).score weights ≤
      (traceCost costs trace).score weights := by
  induction trace with
  | Lit => exact Nat.le_refl _
  | Swap _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [normalize]
      simpa only [traceCost, Cost.score_add] using Nat.add_le_add_right ih _
  | Dup _ _ _ _ trace ih =>
      rw [normalize]
      dsimp only
      split_ifs with hc
      · rw [appendDirect_score]
        simp only [traceCost, Cost.score_add]
        exact Nat.add_le_add ih hc.2
      · simpa only [traceCost, Cost.score_add] using Nat.add_le_add_right ih _

theorem normalize_dupCount_zero (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (value : Value)
    (hcheap : CheapDirect costs weights spills value) :
    Lineage.dupCount value (normalize costs weights trace) = 0 := by
  induction trace with
  | Lit => rfl
  | Swap _ _ _ _ trace ih | Pop _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      rw [normalize]
      exact ih
  | @Dup previous depth hlen hlo hhi trace ih =>
      rw [normalize]
      dsimp only
      split_ifs with hc
      · rw [appendDirect_dupCount, ih]
      · have hn : previous[previous.length - depth]'(by omega) ≠ value := by
          intro he
          exact hc (he ▸ hcheap)
        simp only [Lineage.dupCount, hn, ↓reduceIte, Nat.add_zero, ih]

def normalizeBuilt (costs : PrimitiveCosts) (weights : Weights)
    (built : BuiltTrace spills source target missing) : BuiltTrace spills source target missing :=
  ⟨normalize costs weights built.trace, (normalize_noPop costs weights built.trace).mpr built.noPop,
    (normalize_additions costs weights built.trace).trans built.additions⟩

end Shuffler.Optimality.DirectDominance
