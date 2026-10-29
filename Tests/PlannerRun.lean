import Shuffler.Planner.Run.Defs

namespace PlannerRunTests

open Shuffler

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩

private def distinct (n : ℕ) : Stack := (List.range n).map (fun i => .Var ⟨i⟩)

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

private def summary (source target : Stack) (spills : SpillSet := ∅)
    (spillingAllowed : Bool := false)
    (strategy : BuildMapping.WildcardSlotsStrategy := .Leave) :
    Except ShuffleErr (Bool × SpillSet × List ℕ × Bool) :=
  (Planner.run source target spills spillingAllowed strategy).map fun result =>
    (result.result.isSome, result.state.spills, result.state.dropped.toList.map Fin.val,
      result.sawWildcardCopy)

-- Empty, retained, generated, spilled, and duplicated targets succeed.
#guard succeeds [] []
#guard succeeds [] [.Lit 0, .Wildcard]
#guard succeeds [] [a] {⟨0⟩}
#guard succeeds [a, b] []
#guard succeeds [a, b] [b, a]
#guard succeeds [a, b] [a, a, b, b]
#guard succeeds [.FunctionReturnLabel, b] [b, .FunctionReturnLabel]
#guard succeeds [.FunctionReturnLabel, .FunctionReturnLabel, a]
  [.FunctionReturnLabel, a, .FunctionReturnLabel]
#guard succeeds [.FunctionReturnLabel, .FunctionReturnLabel]
  [.Wildcard, .FunctionReturnLabel, .FunctionReturnLabel] ∅ false .Leave
#guard succeeds [.FunctionReturnLabel, .FunctionReturnLabel]
  [.Wildcard, .FunctionReturnLabel, .FunctionReturnLabel] ∅ false .Take

-- A target cannot request an additional copy of a return label.
#guard match Planner.run [.FunctionReturnLabel] [.FunctionReturnLabel, .FunctionReturnLabel]
    ∅ false .Leave with
  | .error (.assertion "function return label has no bound source") => true
  | _ => false
#guard match Planner.run [.FunctionReturnLabel] [.FunctionReturnLabel, .FunctionReturnLabel]
    ∅ false .Take with
  | .error (.assertion "function return label has no bound source") => true
  | _ => false

-- Unavailable variables and return labels fail the initial availability check.
#guard match Planner.run [] [a] ∅ true .Leave with
  | .error (.assertion "target slot neither on the stack nor generatable") => true
  | _ => false
#guard match Planner.run [] [.FunctionReturnLabel] ∅ false .Leave with
  | .error (.assertion "target slot neither on the stack nor generatable") => true
  | _ => false

-- With no regeneration candidate, resolution fails and keeps the initial planner state.
example : summary (distinct 19) ((distinct 19).drop 1) =
    .ok (false, ∅, List.replicate 19 0, false) := by native_decide

-- A retry drops two source positions and loads their values from new spills.
example : summary (distinct 19) ((distinct 19).drop 1) ∅ true =
    .ok (true, {⟨17⟩, ⟨18⟩}, List.replicate 17 0 ++ [1, 1], false) := by native_decide
#guard succeeds (distinct 19) ((distinct 19).drop 1) ∅ true

-- Existing spills permit the same retry when new spills are disabled.
example : summary (distinct 19) ((distinct 19).drop 1) {⟨17⟩, ⟨18⟩} false =
    .ok (true, {⟨17⟩, ⟨18⟩}, List.replicate 17 0 ++ [1, 1], false) := by native_decide
#guard succeeds (distinct 19) ((distinct 19).drop 1) {⟨17⟩, ⟨18⟩}

-- A failed resolution keeps the drop made before it runs out of candidates.
example : summary ([a, .Lit 0] ++ List.replicate 17 .FunctionReturnLabel)
    ([.Lit 0] ++ List.replicate 17 .FunctionReturnLabel) =
    .ok (false, ∅, [0, 1] ++ List.replicate 17 0, false) := by native_decide

-- A failed resolution also keeps a new spill. Return labels remain undropped.
example : summary ([a, b] ++ List.replicate 17 .FunctionReturnLabel)
    ([b] ++ List.replicate 17 .FunctionReturnLabel) ∅ true =
    .ok (false, {⟨1⟩}, [0, 1] ++ List.replicate 17 0, false) := by native_decide

-- Both wildcard policies record copies taken from wildcard positions.
example : summary [a, b] [.Wildcard, a] ∅ false .Leave =
    .ok (true, ∅, [0, 0], true) := by native_decide
example : summary [a, b] [.Wildcard, a] ∅ false .Take =
    .ok (true, ∅, [0, 0], true) := by native_decide
#guard succeeds [a, b] [.Wildcard, a] ∅ false .Leave
#guard succeeds [a, b] [.Wildcard, a] ∅ false .Take

private def wildcardTarget : Stack :=
  [.Var ⟨17⟩] ++ ((distinct 18).drop 1).take 16 ++ [.Wildcard]

-- A failed plan keeps the wildcard-copy flag as well.
example : summary (distinct 18) wildcardTarget =
    .ok (false, ∅, List.replicate 18 0, true) := by native_decide

-- Leave records the first attempt's wildcard copy even when the last mapping has none.
#guard match Planner.run (distinct 18) wildcardTarget ∅ true .Leave with
  | .error _ => false
  | .ok result =>
    result.result.isSome && result.sawWildcardCopy &&
    match BuildMapping.buildMapping (distinct 18) wildcardTarget result.state.dropped.toList .Leave with
    | .error _ => false
    | .ok builder => !builder.sawWildcardCopy
#guard succeeds (distinct 18) wildcardTarget ∅ true .Leave
#guard succeeds (distinct 18) wildcardTarget ∅ true .Take

-- A return label at a wildcard position is retained under both policies.
example : summary [.FunctionReturnLabel, b] [.Wildcard, .FunctionReturnLabel] ∅ false .Leave =
    .ok (true, ∅, [0, 0], false) := by native_decide
example : summary [.FunctionReturnLabel, b] [.Wildcard, .FunctionReturnLabel] ∅ false .Take =
    .ok (true, ∅, [0, 0], false) := by native_decide

-- SWAP reaches depths 15 and 16; depth 17 needs a retry.
#guard ([15, 16] : List ℕ).all fun depth =>
  succeeds (distinct (depth + 1)) ((distinct (depth + 1)).swap 0 depth)
example : summary (distinct 18) ((distinct 18).swap 0 17) =
    .ok (false, ∅, List.replicate 18 0, false) := by native_decide
#guard succeeds (distinct 18) ((distinct 18).swap 0 17) ∅ true

-- DUP reaches depth 15; depths 16 and 17 need retries.
#guard succeeds (distinct 16) (distinct 16 ++ [a])
#guard ([16, 17] : List ℕ).all fun depth =>
  match summary (distinct (depth + 1)) (distinct (depth + 1) ++ [a]) with
  | .ok (success, spills, dropped, _) =>
    !success && decide (spills = ∅) && dropped.all (· == 0)
  | .error _ => false
#guard ([16, 17] : List ℕ).all fun depth =>
  succeeds (distinct (depth + 1)) (distinct (depth + 1) ++ [a]) ∅ true

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
