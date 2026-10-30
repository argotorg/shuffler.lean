import Shuffler.Planner.Run.Defs

namespace PlannerRunTests

open Shuffler

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩

private def succeeds (source target : Stack) (spills : SpillSet := ∅)
    (spillingAllowed : Bool := false)
    (strategy : BuildMapping.WildcardSlotsStrategy := .Leave) : Bool :=
  match Planner.run source target spills spillingAllowed strategy with
  | .error _ => false
  | .ok result =>
    match result.result with
    | none => false
    | some emitted =>
      decide (StackMatches emitted.stack target) &&
      decide (spills ⊆ result.state.spills) &&
      (spillingAllowed || decide (result.state.spills = spills)) &&
      (List.finRange source.length).all (fun i =>
        !decide source[i].isFunctionReturnLabel || result.state.dropped[i] == 0) &&
      match BuildMapping.buildMapping source target result.state.dropped.toList strategy with
      | .error _ => false
      | .ok builder =>
        (List.finRange source.length).all fun i =>
          decide (emitted.planned_mapping.destinationOf i = builder.mapping.destinationOf i)

private def sampleStacks : ℕ → List Stack
  | 0 => [[]]
  | n + 1 => [] :: (sampleStacks n).flatMap (fun tail =>
      [a, b, .Lit 0, .Wildcard, .FunctionReturnLabel].map (· :: tail))

-- Check available source/target pairs with no additional return labels, both wildcard policies,
-- both spill settings, and both choices of whether new spills are permitted.
example : (sampleStacks 2).all (fun source => (sampleStacks 2).all (fun target =>
    ([∅, {⟨0⟩}] : List SpillSet).all (fun spills =>
      [false, true].all (fun allowed =>
        ([BuildMapping.WildcardSlotsStrategy.Leave, .Take]).all (fun strategy =>
          if target.all (fun slot => decide
              (slot.can_be_freely_generated ∨ slot ∈ source ∨ spills.is_spilled slot)) &&
              decide (target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel) then
            succeeds source target spills allowed strategy
          else true))))) = true := by native_decide

end PlannerRunTests
