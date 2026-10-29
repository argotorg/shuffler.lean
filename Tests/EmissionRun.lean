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

private def sampleStacks : ℕ → List Stack
  | 0 => [[]]
  | n + 1 => [] :: (sampleStacks n).flatMap (fun tail => [a, b, .Lit 0, .Wildcard].map (· :: tail))

-- Every available target of length at most three succeeds under both strategies.
#guard (sampleStacks 3).all fun source => (sampleStacks 3).all fun target =>
  if target.all (fun value => decide (value.can_be_freely_generated ∨ value ∈ source)) then
    succeeds source target .Leave && succeeds source target .Take
  else true

end EmissionRunTests
