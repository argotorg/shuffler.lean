module

public import Theorems.PlannerModel
import all Theorems.PlannerModel
import all ShufflerBridge.Planner.Entry
import all Shuffler.Planner.Run.Theorems

namespace ShufflerVerification

open ShufflerBridge.Planner

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
public theorem planner_model_establishes_correctness (input : PlannerInput)
    (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerModelPostcondition PlannerReturnsCorrectPlanOrBlocked input := by
  obtain ⟨modelResult, modelReturns, matchesTarget⟩ := Shuffler.Planner.run_correct
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
  obtain ⟨modelResult, modelReturns⟩ := Shuffler.Planner.run_ok
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
