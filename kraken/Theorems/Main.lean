module

public import Theorems.PlannerAssembly
public import Theorems.PlannerModel

/-!
# Planner verification

These claims compare parsed x86-64 `Planner::run` with Lean `Shuffler.Planner.run`.
Read `PlannerModel.lean`, then `PlannerAssembly.lean`, then this file.
They give the model claim, result comparison, machine conditions, and combined proofs.

- Valid inputs return Done or Blocked. Assertion exit is excluded.
- Done has a legal abstract trace from the source to a stack that matches the target.
- The general claim also covers model errors, which reach external `exit` with argument 1.
- Postconditions transfer only for results covered by `PlannerResultMatchesModel`.

Proof chain: assembly → flat model → Lean planner.
Binary claims also use recorded layout and separate method-byte checks.

The claims exclude `Shuffle::run` and the external implementation of `exit`.
The compiler, parser, byte checks, hardware, and agreement with Solidity are outside
the Lean proof. The proofs use Lean's core axioms and trusted `bv_decide` results.
-/

namespace ShufflerVerification

/-! ## 1. Assembly and model agreement -/

/-- With the stated machine and input assumptions, the generated method agrees
with the Lean planner model on a plan, a blocked result, or an assertion exit. -/
public theorem planner_assembly_matches_model :
    PlannerAssemblyContract PlannerInputAssumptions PlannerResultMatchesModel :=
  planner_assembly_satisfies_model_contract planner_flat_execution_matches_model

/-- The same claim in the host proved from the recorded binary layout. -/
public theorem planner_binary_matches_model :
    PlannerBinaryContract PlannerInputAssumptions PlannerResultMatchesModel :=
  planner_binary_satisfies_model_contract planner_flat_execution_matches_model

/-! ## 2. Valid inputs exclude assertion exit -/

/-- Valid planner inputs return Done or Blocked. The assertion-exit case is excluded. -/
public theorem planner_assembly_returns_normally :
    PlannerAssemblyNormalReturnContract PlannerInputsValidForNormalReturn
      PlannerResultMatchesModel :=
  planner_assembly_satisfies_normal_return_contract
    (fun input locals assumptions => planner_flat_execution_matches_model input locals
      (PlannerInputsValidForNormalReturn.inputAssumptions input assumptions))
    planner_flat_execution_does_not_assert

/-- The same normal-return claim in the recorded binary host. -/
public theorem planner_binary_returns_normally :
    PlannerBinaryNormalReturnContract PlannerInputsValidForNormalReturn
      PlannerResultMatchesModel :=
  planner_binary_satisfies_normal_return_contract
    (fun input locals assumptions => planner_flat_execution_matches_model input locals
      (PlannerInputsValidForNormalReturn.inputAssumptions input assumptions))
    planner_flat_execution_does_not_assert

/-! ## 3. Transfer any property of the compared results -/

/-- Transfer a postcondition on the compared model results.
The input assumptions must include all `PlannerInputAssumptions`. -/
public theorem planner_assembly_transfers_model_postcondition
    {inputAssumptions : PlannerInput → Prop}
    {postcondition : PlannerInput → PlannerExecutionResult → Prop}
    (representationAssumptions : ∀ input, inputAssumptions input → PlannerInputAssumptions input)
    (modelPostcondition : ∀ input, inputAssumptions input →
      PlannerModelPostcondition postcondition input) :
    PlannerAssemblyContract inputAssumptions postcondition :=
  planner_assembly_satisfies_model_contract
    (fun input locals assumptions => planner_flat_execution_transfers_model_postcondition
      input locals (representationAssumptions input assumptions) postcondition
      (modelPostcondition input assumptions))

/-- Transfer the same class of postconditions in the recorded binary host. -/
public theorem planner_binary_transfers_model_postcondition
    {inputAssumptions : PlannerInput → Prop}
    {postcondition : PlannerInput → PlannerExecutionResult → Prop}
    (representationAssumptions : ∀ input, inputAssumptions input → PlannerInputAssumptions input)
    (modelPostcondition : ∀ input, inputAssumptions input →
      PlannerModelPostcondition postcondition input) :
    PlannerBinaryContract inputAssumptions postcondition :=
  planner_binary_satisfies_model_contract
    (fun input locals assumptions => planner_flat_execution_transfers_model_postcondition
      input locals (representationAssumptions input assumptions) postcondition
      (modelPostcondition input assumptions))

/-! ## 4. Apply the transfer to model correctness -/

/-- The method returns normally. Each Done result has a correct abstract plan. -/
public theorem planner_assembly_returns_correct_plan_or_blocked :
    PlannerAssemblyNormalReturnContract PlannerInputsValidForNormalReturn
      PlannerReturnsCorrectPlanOrBlocked :=
  planner_assembly_satisfies_normal_return_contract
    (fun input locals validInput => planner_flat_execution_transfers_model_postcondition
      input locals (PlannerInputsValidForNormalReturn.inputAssumptions input validInput)
      PlannerReturnsCorrectPlanOrBlocked
      (planner_model_returns_correct_plan_or_blocked input validInput))
    planner_flat_execution_does_not_assert

/-- The same correctness claim in the recorded binary host. -/
public theorem planner_binary_returns_correct_plan_or_blocked :
    PlannerBinaryNormalReturnContract PlannerInputsValidForNormalReturn
      PlannerReturnsCorrectPlanOrBlocked :=
  planner_binary_satisfies_normal_return_contract
    (fun input locals validInput => planner_flat_execution_transfers_model_postcondition
      input locals (PlannerInputsValidForNormalReturn.inputAssumptions input validInput)
      PlannerReturnsCorrectPlanOrBlocked
      (planner_model_returns_correct_plan_or_blocked input validInput))
    planner_flat_execution_does_not_assert

end ShufflerVerification
