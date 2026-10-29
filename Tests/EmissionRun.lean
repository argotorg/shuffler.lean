import Shuffler.Emission.Run.Defs
import Shuffler.BuildMapping.Defs

namespace EmissionRunTests

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩

private def attempt (source target : Stack)
    (strategy : Shuffler.BuildMapping.WildcardSlotsStrategy := .Leave) :
    Except ShuffleErr (Shuffler.Emission.Result source target ∅) := do
  let builder ← Shuffler.BuildMapping.buildMapping source target (List.replicate source.length 0) strategy
  Shuffler.Emission.run source target builder.mapping ∅

private def succeeds (source target : Stack)
    (strategy : Shuffler.BuildMapping.WildcardSlotsStrategy := .Leave) : Bool :=
  match attempt source target strategy with
  | .ok result => result.blocked.isNone && decide (StackMatches result.state.stack target)
  | .error _ => false

#guard succeeds [] []
#guard succeeds [] [.Lit 0, .Wildcard]
#guard succeeds [a, b] []
#guard succeeds [a, b] [b, a]
#guard succeeds [a, b] [a, a, b, b]
#guard succeeds [a, b] [.Wildcard, a] .Leave
#guard succeeds [a, b] [.Wildcard, a] .Take
#guard succeeds [.FunctionReturnLabel, b] [b, .FunctionReturnLabel]
#guard succeeds [.FunctionReturnLabel, .FunctionReturnLabel] [.FunctionReturnLabel, .FunctionReturnLabel]

-- Each target return label needs its own retained source.
#guard match attempt [.FunctionReturnLabel] [.FunctionReturnLabel, .FunctionReturnLabel] with
  | .error (.assertion "function return label has no bound source") => true
  | _ => false

-- A target value that cannot be generated and has no copy is rejected.
#guard match attempt [] [a] with
  | .error (.assertion _) => true
  | _ => false

private def distinct (n : ℕ) : Stack := (List.range n).map (fun i => .Var ⟨i⟩)

-- Surplus removal stops at an unreachable surplus slot.
#guard match attempt (distinct 19) ((distinct 19).drop 1) with
  | .ok result => result.blocked == some ⟨0, 2⟩ && decide (result.state.stack = distinct 19)
  | .error _ => false

-- Lowest-height permutation stops at depth 17.
#guard match attempt (distinct 18) ((distinct 18).swap 0 17) with
  | .ok result => result.blocked == some ⟨0, 1⟩ && decide (result.state.stack = distinct 18)
  | .error _ => false

-- Bottom-up generation cannot DUP the bottom slot at depth 16.
#guard match attempt (distinct 17) (distinct 17 ++ [a]) with
  | .ok result => result.blocked == some ⟨0, 1⟩ && decide (result.state.stack = distinct 17)
  | .error _ => false

-- A block preserves the pop performed earlier in the same attempt.
#guard match attempt (distinct 18 ++ [.Lit 0]) ((distinct 18).drop 1) with
  | .ok result => result.blocked == some ⟨0, 1⟩ && decide (result.state.stack = distinct 18)
  | .error _ => false

private def sampleStacks : ℕ → List Stack
  | 0 => [[]]
  | n + 1 => [] :: (sampleStacks n).flatMap (fun tail => [a, b, .Lit 0, .Wildcard].map (· :: tail))

-- Every available target of length at most three succeeds under both strategies.
#guard (sampleStacks 3).all fun source => (sampleStacks 3).all fun target =>
  if target.all (fun value => decide (value.can_be_freely_generated ∨ value ∈ source)) then
    succeeds source target .Leave && succeeds source target .Take
  else true

end EmissionRunTests
