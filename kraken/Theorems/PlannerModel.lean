module

public import Theorems.PlannerInput
import all Theorems.ValueEncoding
import all Shuffler.Planner.Run.Theorems
import all ShufflerBridge.Planner.Entry

/-!
# 1. The planner model

Read `PlannerInput.lean` and `ValueEncoding.lean` for the input types and encodings.
This file states correctness of the actual Lean planner, defines the compared
results, and proves their agreement with the flat model. Then read
`PlannerAssembly.lean` and `Main.lean`.

`StackMatches` requires equal lengths and equal values at non-wildcard positions.
A plan contains `Trace finalSpills source output`: legal abstract stack operations.
Loads use the final spill set. Spill-memory contents and EVM execution are outside
this claim. Blocked is allowed; completeness and optimality are not proved.
-/

namespace ShufflerVerification

open Shuffler ShufflerBridge.Emission ShufflerBridge.Planner

/-! ## Correctness of the actual planner

These are the model preconditions. No representation or machine assumptions occur
here. A returned plan must match the target; its trace type proves legal operations.
-/

theorem planner_model_correct (source target : Stack) (spills : SpillSet)
    (spillingAllowed : Bool) (strategy : BuildMapping.WildcardSlotsStrategy)
    (targetValuesAreAvailable : ∀ value ∈ target,
      value.is_junk ∨ value.can_be_freely_generated ∨ value ∈ source ∨ spills.is_spilled value)
    (sourceHasEnoughReturnLabels :
      target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel) :
    ∃ result, Shuffler.Planner.run source target spills spillingAllowed strategy = .ok result ∧
      ∀ plan, result.result = some plan → StackMatches plan.stack target :=
  Shuffler.Planner.run_correct source target spills spillingAllowed strategy
    targetValuesAreAvailable sourceHasEnoughReturnLabels

/-! ## Representation assumptions -/

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

/-! ## Connect the comparison to the flat execution -/

private theorem inputAssumptions_iff_bridgeAssumptions (input : PlannerInput) :
    PlannerInputAssumptions input ↔
      input.planner.m.toNat ≤ FlatShuffler.MAX_N ∧
      input.planner.n.toNat ≤ FlatShuffler.MAX_N ∧
      SlotsOk (input.sourceSlots ++ input.targetSlots) ∧
      DnR (Vector.replicate (srcOf input.planner.source input.planner.m).length
        (0 : Byte)) input.initialState.dropped := by
  constructor
  · intro assumptions
    exact ⟨assumptions.sourceSizeFitsBuffer, assumptions.targetSizeFitsBuffer,
      ⟨assumptions.slotsHaveCanonicalEncoding, assumptions.slotKindsAreSupported,
        assumptions.variablePayloadIdentifiesSlot⟩,
      fun position => by
        have positionBound : position.val < input.sourceSlots.length := by
          simpa only [srcOf, PlannerInput.sourceSlots, List.length_map] using position.isLt
        have zeroByte := assumptions.sourceDroppedBytesAreZero ⟨position.val, positionBound⟩
        simp only [Fin.getElem_fin, Vector.getElem_replicate]
        rw [zeroByte]
        rfl⟩
  · rintro ⟨sourceSize, targetSize, slots, dropped⟩
    exact ⟨sourceSize, targetSize, slots.canon, slots.kind, slots.inj,
      fun position => by
        have positionBound : position.val < (srcOf input.planner.source input.planner.m).length := by
          simpa only [srcOf, PlannerInput.sourceSlots, List.length_map] using position.isLt
        have byteEquality : (0 : Byte) =
            (FlatShuffler.Flat.get input.initialState.dropped (.ofNat 64 position.val)).toFin := by
          simpa only [Fin.getElem_fin, Vector.getElem_replicate]
            using dropped ⟨position.val, positionBound⟩
        exact BitVec.eq_of_toFin_eq byteEquality.symm⟩

private theorem resultComparison_iff_bridgeRelation (input : PlannerInput)
    (execution : PlannerExecutionResult) :
    PlannerResultMatchesModel input execution ↔
      RunR input.planner execution
        (Shuffler.Planner.run (srcOf input.planner.source input.planner.m)
          (srcOf input.planner.target input.planner.n)
          (pSpills input.sourceSlots input.planner.n.toNat input.planner.target
            input.initialState.spills)
          input.planner.allowed (if input.takeWildcardSlots then .Take else .Leave)) := by
  rcases execution with ⟨status, finalState⟩
  simp only [PlannerResultMatchesModel, PlannerInput.sourceStack, PlannerInput.targetStack,
    PlannerInput.spillsFromBytes, PlannerInput.sourceSlots, PlannerInput.targetSlots,
    RunR, SRpl, DnR, srcOf, pSpills, FlatShuffler.Flat.listEnv,
    ShufflerBridge.Emission.decodeOptionalSourceIndex, FlatShuffler.Flat.optOf,
    FlatShuffler.Flat.NONE, and_assoc]
  split <;> simp_all only
  rename_i modelResult modelEquation
  cases modelResult.result <;> rfl

/-- The flat execution agrees with the model for every initial value of local arrays. -/
public theorem planner_flat_execution_matches_model
    (input : PlannerInput) (initialLocalValues : Nat → FlatShuffler.Flat.RunU)
    (assumptions : PlannerInputAssumptions input) :
    PlannerResultMatchesModel input (input.execute initialLocalValues) := by
  obtain ⟨sourceSize, targetSize, slots, dropped⟩ :=
    (inputAssumptions_iff_bridgeAssumptions input).mp assumptions
  exact (resultComparison_iff_bridgeRelation input _).mpr
    (plannerRun_corr sourceSize targetSize slots input.takeWildcardSlots
      input.initialState initialLocalValues dropped)

/-- Valid planner inputs include the representation assumptions of the comparison. -/
public theorem PlannerInputsValidForNormalReturn.inputAssumptions
    (input : PlannerInput) (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerInputAssumptions input :=
  validInput.1

/-- Transfer a postcondition of the compared model result to the flat execution. -/
public theorem planner_flat_execution_transfers_model_postcondition
    (input : PlannerInput) (initialLocalValues : Nat → FlatShuffler.Flat.RunU)
    (assumptions : PlannerInputAssumptions input)
    (post : PlannerInput → PlannerExecutionResult → Prop)
    (modelPostcondition : PlannerModelPostcondition post input) :
    post input (input.execute initialLocalValues) :=
  modelPostcondition _
    (planner_flat_execution_matches_model input initialLocalValues assumptions)

/-- Each compared Done result has the model's legal trace and target stack. -/
public theorem planner_model_returns_correct_plan_or_blocked (input : PlannerInput)
    (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerModelPostcondition PlannerReturnsCorrectPlanOrBlocked input := by
  obtain ⟨modelResult, modelReturns, matchesTarget⟩ := planner_model_correct
    input.sourceStack input.targetStack (input.spillsFromBytes input.initialState.spills)
    input.planner.allowed (if input.takeWildcardSlots then .Take else .Leave)
    validInput.2.1 validInput.2.2
  intro execution comparisonResult
  rcases execution with ⟨status, finalState⟩
  simp only [PlannerResultMatchesModel, modelReturns] at comparisonResult
  obtain ⟨spillsMatch, _, _, _, outcome⟩ := comparisonResult
  change status = .blocked ∨ _
  cases planEquation : modelResult.result with
  | none =>
    simp only [planEquation] at outcome
    exact Or.inl outcome
  | some plan =>
    simp only [planEquation] at outcome
    have stackMatches := matchesTarget plan planEquation
    refine Or.inr ⟨outcome.1, plan.stack, stackMatches, ?_⟩
    rw [← spillsMatch]
    refine ⟨plan.trace, ?_, outcome.2.2.1⟩
    simpa only [stackMatches.length_eq] using outcome.2.1

private theorem valid_model_result_excludes_assertion (input : PlannerInput)
    (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerModelPostcondition (fun _ execution => execution.1 ≠ .assertionFailed) input := by
  rcases validInput with ⟨_, availableTargets, enoughReturnLabels⟩
  obtain ⟨modelResult, modelReturns, _⟩ := planner_model_correct
    input.sourceStack input.targetStack (input.spillsFromBytes input.initialState.spills)
    input.planner.allowed (if input.takeWildcardSlots then .Take else .Leave)
    availableTargets enoughReturnLabels
  intro execution comparisonResult
  rcases execution with ⟨status, finalState⟩
  simp only [PlannerResultMatchesModel, modelReturns] at comparisonResult
  obtain ⟨_, _, _, _, outcome⟩ := comparisonResult
  cases planEquation : modelResult.result with
  | none =>
    simp only [planEquation] at outcome
    rw [outcome]
    change FlatShuffler.Flat.Status.blocked ≠ .assertionFailed
    decide
  | some plan =>
    simp only [planEquation] at outcome
    rw [outcome.1]
    change FlatShuffler.Flat.Status.done ≠ .assertionFailed
    decide

/-- With valid input, the flat execution returns Done or Blocked for every local-array value. -/
public theorem planner_flat_execution_does_not_assert
    (input : PlannerInput) (initialLocalValues : Nat → FlatShuffler.Flat.RunU)
    (validInput : PlannerInputsValidForNormalReturn input) :
    (input.execute initialLocalValues).1 ≠ .assertionFailed :=
  planner_flat_execution_transfers_model_postcondition input initialLocalValues validInput.1
    (fun _ execution => execution.1 ≠ .assertionFailed)
    (valid_model_result_excludes_assertion input validInput)

end ShufflerVerification
