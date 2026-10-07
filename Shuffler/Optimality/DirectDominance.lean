import Shuffler.Optimality.Baseline
import Shuffler.Optimality.Lineage

namespace Shuffler.Optimality.DirectDominance

def CheapDirect (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (value : Value) : Prop :=
  Shuffler.Placement.Free spills value ∧
    directPrice costs weights spills value ≤ costs.dup.score weights

instance (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) (value : Value) :
    Decidable (CheapDirect costs weights spills value) := by
  unfold CheapDirect
  infer_instance

def appendDirect (trace : Trace spills source target) (value : Value)
    (hfree : Shuffler.Placement.Free spills value) : Trace spills source (target ++ [value]) := by
  cases value with
  | Lit value => exact .Push (.Lit value) (by trivial) trace
  | Wildcard => exact .Push .Wildcard (by trivial) trace
  | Var id =>
      have hs : id ∈ spills := by
        simpa only [Shuffler.Placement.Free, Value.can_be_freely_generated,
          SpillSet.is_spilled, false_or] using hfree
      exact .Load id hs trace
  | FunctionReturnLabel =>
      simp [Shuffler.Placement.Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

-- The replacement is one instruction with exactly the same stack effect.
-- Unavailable direct operations are excluded even when directPrice uses
-- its finite DUP-price fallback.
def normalize (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) : Trace spills source target := by
  cases trace with
  | Lit => exact .Lit source
  | Swap depth hlen hlo hhi earlier =>
      exact .Swap depth hlen hlo hhi (normalize costs weights earlier)
  | @Dup previous depth hlen hlo hhi earlier =>
      let value := previous[previous.length - depth]'(by omega)
      if hc : CheapDirect costs weights spills value then
        exact appendDirect (normalize costs weights earlier) value hc.1
      else exact .Dup depth hlen hlo hhi (normalize costs weights earlier)
  | Pop hlen earlier => exact .Pop hlen (normalize costs weights earlier)
  | Push value hfree earlier => exact .Push value hfree (normalize costs weights earlier)
  | Load id hspill earlier => exact .Load id hspill (normalize costs weights earlier)
termination_by structural trace

-- Include the initial stack, then the concrete stack after each step.
def statePath : Trace spills source target → List Stack
  | .Lit _ => [source]
  | @Trace.Swap _ _ previous depth _ _ _ earlier =>
      statePath earlier ++ [previous.swap (previous.length - 1) (previous.length - 1 - depth)]
  | @Trace.Dup _ _ previous depth hlen hlo _ earlier =>
      statePath earlier ++ [previous ++ [previous[previous.length - depth]'(by omega)]]
  | @Trace.Pop _ _ previous _ earlier => statePath earlier ++ [previous.dropLast]
  | @Trace.Push _ _ previous value _ earlier => statePath earlier ++ [previous ++ [value]]
  | @Trace.Load _ _ previous id _ earlier => statePath earlier ++ [previous ++ [.Var id]]

end Shuffler.Optimality.DirectDominance
