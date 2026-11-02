module

public import FlatShuffler.FlatPlan

@[expose] public section

namespace ShufflerVerification

/-- The arguments and buffer contents at entry to `Planner::run`.
`initialState` includes the spill bytes, dropped bytes, wildcard-copy flag,
data buffer, operation trace, and source-index buffer. -/
structure PlannerInput where
  planner : FlatShuffler.Flat.Planner
  takeWildcardSlots : Bool
  initialState : FlatShuffler.Flat.PSt

/-- The active slots exclude the unused tail of each fixed-size buffer. -/
def PlannerInput.sourceSlots (input : PlannerInput) : List FlatShuffler.StackSlot :=
  input.planner.source.toList.take input.planner.m.toNat

def PlannerInput.targetSlots (input : PlannerInput) : List FlatShuffler.StackSlot :=
  input.planner.target.toList.take input.planner.n.toNat

/-- The status and final buffers of the flat execution model.
`.assertionFailed` represents an assertion exit, not a C++ return value. -/
abbrev PlannerExecutionResult := FlatShuffler.Flat.Status × FlatShuffler.Flat.PSt

/-- Each attempt can start with arbitrary values in its local arrays.
The assembly and model proofs cover every such choice. -/
def PlannerInput.execute (input : PlannerInput)
    (initialLocalValues : Nat → FlatShuffler.Flat.RunU) : PlannerExecutionResult :=
  FlatShuffler.Flat.plannerRun input.planner input.takeWildcardSlots
    input.initialState initialLocalValues

end ShufflerVerification
