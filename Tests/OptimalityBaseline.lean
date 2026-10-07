import Shuffler.Optimality.Baseline.Theorems

namespace Tests.OptimalityBaseline

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def zero : Value := .Lit 0
private def wide : Value := .Lit (2 ^ 248)

private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun value => if value = zero then .push0 else .push ⟨31, by decide⟩)
  (fun _ => .push ⟨1, by decide⟩)

#guard baseline costs Weights.bytesOnly ∅ [] 0 = 0
#guard baseline costs Weights.bytesOnly ∅ [] {wide, wide} = 34
#guard baseline costs Weights.bytesOnly ∅ [wide] {wide, wide} = 2
#guard baseline costs Weights.gasOnly ∅ [] {zero, zero} = 4
#guard baseline costs Weights.gasOnly {⟨0⟩} [] {a, a} = 9
#guard baseline costs Weights.bytesOnly {⟨0⟩} [] {a, a} = 5
#guard baseline costs Weights.gasOnly {⟨0⟩} [a] {a, a} = 6

-- Absent values that cannot be introduced get a finite fallback price.
-- The bound does not assert that a trace for such a request exists.
#guard baseline costs Weights.bytesOnly ∅ [] {a} = 1
#guard baseline costs Weights.bytesOnly ∅ [] {.FunctionReturnLabel} = 1

example (trace : Trace spills source target) (h : Eligible missing trace) :
    baseline costs weights spills source missing ≤ (traceCost costs trace).score weights :=
  baseline_le_score_of_eligible costs weights trace h

example (trace : Trace spills source target) (h : Eligible missing trace) :
    baseline costs weights spills source missing + costs.swap.score weights * trace.swapCount ≤
      (traceCost costs trace).score weights :=
  baseline_add_swapCost_le_score_of_eligible costs weights trace h

end Tests.OptimalityBaseline
