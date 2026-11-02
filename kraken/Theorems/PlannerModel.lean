module

public import Theorems.PlannerInput
import all Theorems.ValueEncoding
import all Shuffler.Planner.Run.Defs

/-!
# The model claim: inputs, decoding, and results

Read this file in order. The assumptions below are the full additional assumptions
for the model comparison. The assembly contract adds buffer and register conditions.
The definitions below are the specification; they do not import correspondence proofs.
-/

namespace ShufflerVerification

open Shuffler ShufflerBridge.Emission

/-- Size, slot encoding, variable identity, and initial dropped-byte conditions.
They permit unavailable targets and excess function return labels. The general
comparison therefore includes model errors. -/
public structure PlannerInputAssumptions (input : PlannerInput) : Prop where
  sourceSizeFitsBuffer : input.planner.m.toNat ≤ FlatShuffler.MAX_N
  targetSizeFitsBuffer : input.planner.n.toNat ≤ FlatShuffler.MAX_N
  slotsHaveCanonicalEncoding :
    ∀ slot ∈ input.sourceSlots ++ input.targetSlots,
      (slot.kind = FlatShuffler.Junk → slot = .junk) ∧
      (slot.kind = FlatShuffler.FunctionReturnLabel →
        slot = ⟨0, FlatShuffler.FunctionReturnLabel, FlatShuffler.Unreachable⟩)
  slotKindsAreSupported :
    ∀ slot ∈ input.sourceSlots ++ input.targetSlots, slot.kind.toNat < 4
  variablePayloadIdentifiesSlot :
    ∀ first ∈ input.sourceSlots ++ input.targetSlots,
    ∀ second ∈ input.sourceSlots ++ input.targetSlots,
      FlatShuffler.Flat.isVariable first = true →
      FlatShuffler.Flat.isVariable second = true →
      first.payload = second.payload → first = second
  sourceDroppedBytesAreZero :
    ∀ position : Fin input.sourceSlots.length,
      FlatShuffler.Flat.get input.initialState.dropped (.ofNat 64 position.val) = 0

/-! ## Decode the input

`ValueEncoding.lean` defines the slot identity, value decoding, spill-set decoding,
and operation encoding. The bridge proofs use those same definitions.
-/

def PlannerInput.sourceStack (input : PlannerInput) : Stack :=
  input.sourceSlots.map decodeStackSlot

def PlannerInput.targetStack (input : PlannerInput) : Stack :=
  input.targetSlots.map decodeStackSlot

/-- Only variables present in the source or target enter the model spill set.
A variable is spilled when its payload-indexed byte is nonzero. -/
def PlannerInput.spillsFromBytes (input : PlannerInput)
    (spillBytes : BitVec 32 → BitVec 8) : SpillSet :=
  spilledVariables
    ⟨input.targetSlots, fun payload => UInt8.ofBitVec (spillBytes (.ofNat 32 payload))⟩
    input.sourceStack

/-! ## Inputs that exclude assertion failure

These sufficient conditions add target availability and enough source function
return labels. They permit Done or Blocked and exclude all model errors, including
the internal assertion checks on each attempt. They do not require that a plan exists.
-/

public def PlannerInputsValidForNormalReturn (input : PlannerInput) : Prop :=
  PlannerInputAssumptions input ∧
  (∀ value ∈ input.targetStack,
    value.is_junk ∨ value.can_be_freely_generated ∨ value ∈ input.sourceStack ∨
      (input.spillsFromBytes input.initialState.spills).is_spilled value) ∧
  input.targetStack.count .FunctionReturnLabel ≤ input.sourceStack.count .FunctionReturnLabel

/-! ## Compare the result

Done and Blocked compare spills, the spilling policy, active dropped bytes, and the
wildcard-copy flag. Done also compares the active output stack, operation sequence,
and original-source index at each target position. Blocked does not compare these
three outputs. The spill set includes only input source and target variables.
Unused buffer tails and padding are outside the comparison. A model error compares
only the failure outcome; its error value and final high-level state are not compared.
-/

public def PlannerResultMatchesModel (input : PlannerInput)
    (execution : PlannerExecutionResult) : Prop :=
  let (status, finalState) := execution
  match Shuffler.Planner.run input.sourceStack input.targetStack
      (input.spillsFromBytes input.initialState.spills) input.planner.allowed
      (if input.takeWildcardSlots then .Take else .Leave) with
  | .error _ => status = .assertionFailed
  | .ok modelResult =>
    modelResult.state.spills = input.spillsFromBytes finalState.spills ∧
    modelResult.state.spillingAllowed = input.planner.allowed ∧
    (∀ position : Fin input.sourceStack.length,
      modelResult.state.dropped[position] =
        (FlatShuffler.Flat.get finalState.dropped (.ofNat 64 position.val)).toFin) ∧
    finalState.saw = modelResult.sawWildcardCopy ∧
    match modelResult.result with
    | none => status = .blocked
    | some plan =>
      status = .done ∧
      (finalState.data.toList.take plan.stack.length).map decodeStackSlot = plan.stack ∧
      finalState.trace = (traceOperations plan.trace).map encodeTraceOperation ∧
      ∀ targetPosition : Fin input.targetStack.length,
        decodeOptionalSourceIndex
          (FlatShuffler.Flat.get finalState.sources (.ofNat 64 targetPosition.val)) =
            (plan.planned_mapping.symm targetPosition).map Fin.val

/-- Blocked is allowed. Done has a legal abstract trace from source to target.
Target wildcards accept any value. Loads use the final spill set; this does not
prove that spill memory contains those values or that EVM execution is correct. -/
public def PlannerReturnsCorrectPlanOrBlocked (input : PlannerInput)
    (execution : PlannerExecutionResult) : Prop :=
  execution.1 = .blocked ∨
    (execution.1 = .done ∧ ∃ stack : Stack,
      StackMatches stack input.targetStack ∧
      ∃ trace : Trace (input.spillsFromBytes execution.2.spills) input.sourceStack stack,
        (execution.2.data.toList.take input.targetStack.length).map decodeStackSlot = stack ∧
        execution.2.trace = (traceOperations trace).map encodeTraceOperation)

/-- The actual Lean planner result establishes `post` for every result admitted by
its comparison. The comparison defines which observations a postcondition can use.
It does not preserve error text or the unused parts of output buffers. -/
public def PlannerModelPostcondition
    (post : PlannerInput → PlannerExecutionResult → Prop) (input : PlannerInput) : Prop :=
  ∀ execution, PlannerResultMatchesModel input execution → post input execution

end ShufflerVerification
