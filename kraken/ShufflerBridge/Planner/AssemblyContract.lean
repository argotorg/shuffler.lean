module

public import Theorems.PlannerAssembly
import all Theorems.PlannerAssembly
import all FlatShuffler.PlanFinal

namespace ShufflerVerification

open FlatShuffler FlatShuffler.Unit
open Std.WP Lean.Order
open scoped Program.WP

private theorem nativePrecondition_of_reviewPrecondition
    {inputAssumptions : PlannerInput → Prop}
    {plannerAddress : Addr} {memory : PlannerCallMemory} {frame : MProp 64} {entry : MachineData}
    (pre : PlannerCallPrecondition inputAssumptions plannerAddress memory frame entry) :
    VPre plannerCallOwnedMemory PlannerCallMemory.Ok plannerAddress memory frame plannerRunA plannerRunD entry :=
  ⟨pre.plannerAddressInRegister,
    ⟨⟨pre.sourceSizeFitsBuffer, pre.targetSizeFitsBuffer,
      pre.sourceBufferLength, pre.targetBufferLength⟩,
      pre.spillByteCountFitsAddress, pre.sourceVariableIdsFitSpillBuffer,
      pre.targetVariableIdsFitSpillBuffer, pre.operationBufferLength, pre.traceLengthFitsBuffer⟩,
    ⟨pre.bufferAddressesInRegisters.1, pre.bufferAddressesInRegisters.2.1,
      pre.bufferAddressesInRegisters.2.2.1, pre.bufferAddressesInRegisters.2.2.2,
      pre.traceStartsEmpty⟩,
    pre.ownsMemoryAndStack⟩

private theorem reviewPrecondition_iff_nativePrecondition
    {inputAssumptions : PlannerInput → Prop}
    {plannerAddress : Addr} {memory : PlannerCallMemory} {frame : MProp 64}
    {entry : MachineData} :
    PlannerCallPrecondition inputAssumptions plannerAddress memory frame entry ↔
      VPre plannerCallOwnedMemory PlannerCallMemory.Ok plannerAddress memory frame
        plannerRunA plannerRunD entry ∧ inputAssumptions (plannerInputAtEntry memory entry) := by
  constructor
  · intro pre
    exact ⟨nativePrecondition_of_reviewPrecondition pre, pre.modelInputAssumptions⟩
  · rintro ⟨pre, modelAssumptions⟩
    exact ⟨pre.rdi, pre.ok.planner.m, pre.ok.planner.n,
      pre.ok.planner.sw, pre.ok.planner.tw, pre.ok.spillCount,
      pre.ok.sourceIds, pre.ok.targetIds, pre.ok.ops, pre.ok.traceLength,
      ⟨pre.args.1, pre.args.2.1, pre.args.2.2.1, pre.args.2.2.2.1⟩,
      pre.args.2.2.2.2, pre.mem, modelAssumptions⟩

private theorem reviewReturn_of_nativeReturn
    {resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop}
    {plannerAddress : Addr} {before : PlannerCallMemory} {frame : MProp 64}
    {entry returned : MachineData}
    (comparison : ∀ initialLocalValues, resultMatchesModel (plannerInputAtEntry before entry)
      ((plannerInputAtEntry before entry).execute initialLocalValues))
    (post : VPost plannerCallOwnedMemory PlannerCallMemory.Ok plannerAddress frame plannerRunD
      (fun after returned => plannerRunNormalReturn before after entry returned) entry returned) :
    PlannerNormalReturn resultMatchesModel plannerAddress before frame entry returned := by
  obtain ⟨after, ⟨⟨locals, returnByte, finalState, objectFields, dataAddress,
    operationsAddress, sourcesAddress, countAddress, spillCount, count⟩, normalByte⟩,
    valid, owned⟩ := post
  change al returned = code ((plannerInputAtEntry before entry).execute locals).1 at returnByte
  have modelStatusIsNormal :
      ((plannerInputAtEntry before entry).execute locals).1 ≠ .assertionFailed := by
    intro failed
    exact normalByte (by rw [returnByte, failed]; rfl)
  exact ⟨after, valid, owned,
    ⟨objectFields, dataAddress, operationsAddress, sourcesAddress, countAddress, spillCount⟩,
    locals, returnByte, modelStatusIsNormal, finalState, count, comparison locals⟩

private theorem reviewExit_of_nativeExit
    {resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop}
    {plannerAddress : Addr} {before : PlannerCallMemory} {frame : MProp 64}
    {entry exiting : MachineData}
    (comparison : ∀ initialLocalValues, resultMatchesModel (plannerInputAtEntry before entry)
      ((plannerInputAtEntry before entry).execute initialLocalValues))
    (post : VPost plannerCallOwnedMemory PlannerCallMemory.Ok plannerAddress frame plannerRunD
      (fun after exiting => plannerRunX before after entry exiting) entry exiting) :
    PlannerAssertionExit resultMatchesModel plannerAddress before frame entry exiting := by
  obtain ⟨after, ⟨locals, failed, finalState, objectFields, dataAddress,
    operationsAddress, sourcesAddress, countAddress, spillCount, count⟩, valid, owned⟩ := post
  exact ⟨after, valid, owned,
    ⟨objectFields, dataAddress, operationsAddress, sourcesAddress, countAddress, spillCount⟩,
    count, locals, failed, finalState, comparison locals⟩

public theorem planner_assembly_satisfies_model_contract
    {inputAssumptions : PlannerInput → Prop}
    {resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop}
    (comparison : ∀ input initialLocalValues, inputAssumptions input →
      resultMatchesModel input (input.execute initialLocalValues)) :
    PlannerAssemblyContract inputAssumptions resultMatchesModel := by
  intro _ linkedMethods exitBoundary
  let := linkedMethods.plannerDecls
  intro plannerAddress memory frame entry returnAddress
  refine ⟨fun current ⟨atEntry, pre⟩ => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨address, post, registers⟩ => Or.inl
        ⟨address, reviewReturn_of_nativeReturn
          (fun locals => comparison _ locals pre.modelInputAssumptions) post, registers⟩)
      (fun ⟨address, exitCode, post⟩ => Or.inr
        ⟨address, exitCode, reviewExit_of_nativeExit
          (fun locals => comparison _ locals pre.modelInputAssumptions) post⟩))
    ((FlatShuffler.plan_correct linkedMethods exitBoundary plannerAddress memory frame
      entry returnAddress).le_wp current
        ⟨atEntry, (reviewPrecondition_iff_nativePrecondition.mp pre).1⟩)

public theorem planner_binary_satisfies_model_contract
    {inputAssumptions : PlannerInput → Prop}
    {resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop}
    (comparison : ∀ input initialLocalValues, inputAssumptions input →
      resultMatchesModel input (input.execute initialLocalValues)) :
    PlannerBinaryContract inputAssumptions resultMatchesModel :=
  planner_assembly_satisfies_model_contract comparison binLinked binBoundary

public theorem planner_assembly_satisfies_normal_return_contract
    {inputAssumptions : PlannerInput → Prop}
    {resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop}
    (comparison : ∀ input initialLocalValues, inputAssumptions input →
      resultMatchesModel input (input.execute initialLocalValues))
    (doesNotAssert : ∀ input initialLocalValues, inputAssumptions input →
      (input.execute initialLocalValues).1 ≠ .assertionFailed) :
    PlannerAssemblyNormalReturnContract inputAssumptions resultMatchesModel := by
  intro _ linkedMethods exitBoundary
  let := linkedMethods.plannerDecls
  intro plannerAddress memory frame entry returnAddress
  refine ⟨fun current ⟨atEntry, pre⟩ => ?_⟩
  apply Program.wp_mono (fun _ h => h) ?_
    ((planner_assembly_satisfies_model_contract comparison linkedMethods exitBoundary
      plannerAddress memory frame entry returnAddress).le_wp current ⟨atEntry, pre⟩)
  intro finished result
  rcases result with normalReturn | ⟨_, _, assertionExit⟩
  · exact normalReturn
  · obtain ⟨after, valid, owned, fields, count, locals, failed, finalState,
      comparison⟩ := assertionExit
    exact False.elim (doesNotAssert _ locals pre.modelInputAssumptions failed)

public theorem planner_binary_satisfies_normal_return_contract
    {inputAssumptions : PlannerInput → Prop}
    {resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop}
    (comparison : ∀ input initialLocalValues, inputAssumptions input →
      resultMatchesModel input (input.execute initialLocalValues))
    (doesNotAssert : ∀ input initialLocalValues, inputAssumptions input →
      (input.execute initialLocalValues).1 ≠ .assertionFailed) :
    PlannerBinaryNormalReturnContract inputAssumptions resultMatchesModel :=
  planner_assembly_satisfies_normal_return_contract comparison doesNotAssert binLinked binBoundary

end ShufflerVerification
