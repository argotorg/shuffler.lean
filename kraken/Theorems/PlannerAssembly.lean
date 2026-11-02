module

public import Theorems.PlannerInput
import all FlatShuffler.Unit.Plan.PlannerRunDefs
import all FlatShuffler.PlannerLink
import all FlatShuffler.BinHost
import all FlatShuffler.PlanFinal

/-!
# 2. The assembly contract

Read `NativeInterface.lean` for the planner object, buffers, and memory views.
This file defines all machine preconditions and effects, then connects the contract
to the instruction proof. `Main.lean` combines this result with `PlannerModel.lean`.

The separation operator `∗` requires disjoint owned regions. `frame` is arbitrary
caller memory and is preserved. Stack storage is measured in eight-byte words:
8240 free words plus a return slot. The exit contract stops at external `exit(1)`.
The final normal-return theorems exclude that outcome for valid inputs.
-/

namespace ShufflerVerification

open FlatShuffler FlatShuffler.Unit FlatShuffler.Sep
open Std.WP Lean.Order
open scoped Program.WP

/-- Decode the C++ Boolean argument from the low byte of `%rsi`.
`PlannerObjectMemory.fl` decodes source and target words and the nonzero spilling-policy byte. -/
def plannerInputAtEntry (memory : PlannerCallMemory) (entry : MachineData) : PlannerInput :=
  ⟨memory.p.fl, (rsi entry).setWidth 8 == 1#8, memory.state⟩

/-- Own 8240 free stack words, a return slot, and the given memory.
The postconditions use the entry stack pointer, including at the exit boundary. -/
def PlannerStackAndMemory (ownedMemory : MProp 64) (entry : MachineData)
    (currentMemory : Mem 64) : Prop :=
  ∃ freeStackWords returnSlot,
    freeStackWords.length = 8240 ∧
    (Stk (rsp entry) freeStackWords returnSlot ∗ ownedMemory).get currentMemory

/-- All machine assumptions. Model-specific assumptions are the last field.
No condition on the initial values of local mapping arrays is required. -/
structure PlannerCallPrecondition (inputAssumptions : PlannerInput → Prop)
    (plannerAddress : Addr) (memory : PlannerCallMemory) (frame : MProp 64)
    (entry : MachineData) : Prop where
  plannerAddressInRegister : rdi entry = plannerAddress
  sourceSizeFitsBuffer : memory.p.sourceSize.toNat ≤ maxStackSize
  targetSizeFitsBuffer : memory.p.targetSize.toNat ≤ maxStackSize
  sourceBufferLength : memory.p.sw.length = memory.p.sourceSize.toNat
  targetBufferLength : memory.p.tw.length = memory.p.targetSize.toNat
  spillByteCountFitsAddress : memory.spillCount ≤ 2 ^ 32
  sourceVariableIdsFitSpillBuffer : ∀ id ∈ splIds memory.p.sw, id < memory.spillCount
  targetVariableIdsFitSpillBuffer : ∀ id ∈ splIds memory.p.tw, id < memory.spillCount
  operationBufferLength : memory.ops.length = 6 * memory.p.targetSize.toNat + 4 * memory.p.sourceSize.toNat
  traceLengthFitsBuffer : memory.traceLength ≤ memory.ops.length
  bufferAddressesInRegisters : rdx entry = memory.dataPtr ∧ rcx entry = memory.opsPtr ∧
    r8 entry = memory.sourcesPtr ∧ r9 entry = memory.countPtr
  traceStartsEmpty : memory.traceLength = 0
  ownsMemoryAndStack : PlannerStackAndMemory (plannerCallOwnedMemory plannerAddress memory ∗ frame)
    entry entry.dmem
  modelInputAssumptions : inputAssumptions (plannerInputAtEntry memory entry)

/-- These object fields and buffer addresses are preserved on return and exit.
The wildcard-copy byte and mutable buffer contents can change. -/
def PlannerObjectAndAddressesPreserved (before after : PlannerCallMemory) : Prop :=
  after.p = { before.p with saw := after.p.saw } ∧
  after.dataPtr = before.dataPtr ∧ after.opsPtr = before.opsPtr ∧
  after.sourcesPtr = before.sourcesPtr ∧ after.countPtr = before.countPtr ∧
  after.spillCount = before.spillCount

/-- Normal return permits only success or a blocked result.
It compares the return byte and final buffers with the model.
On success, the count word equals the operation count. Otherwise it keeps its entry value. -/
def PlannerNormalReturn (resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop)
    (plannerAddress : Addr) (before : PlannerCallMemory) (frame : MProp 64)
    (entry returned : MachineData) : Prop :=
  ∃ after : PlannerCallMemory,
    after.Ok ∧
    PlannerStackAndMemory (plannerCallOwnedMemory plannerAddress after ∗ frame) entry returned.dmem ∧
    PlannerObjectAndAddressesPreserved before after ∧
    ∃ initialLocalValues,
      let execution := (plannerInputAtEntry before entry).execute initialLocalValues
      some (al returned) = code execution.1 ∧ execution.1 ≠ .assertionExit ∧ after.state = execution.2 ∧
      after.count = (if execution.1 = .returned .done then .ofNat 64 execution.2.trace.length
        else before.count) ∧
      resultMatchesModel (plannerInputAtEntry before entry) execution

/-- An assertion reaches external `exit(1)` with matching model failure.
The count word is unchanged. The caller's frame is still present at that boundary. -/
def PlannerAssertionExit (resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop)
    (plannerAddress : Addr) (before : PlannerCallMemory) (frame : MProp 64)
    (entry exiting : MachineData) : Prop :=
  ∃ after : PlannerCallMemory,
    after.Ok ∧
    PlannerStackAndMemory (plannerCallOwnedMemory plannerAddress after ∗ frame) entry exiting.dmem ∧
    PlannerObjectAndAddressesPreserved before after ∧ after.count = before.count ∧
    ∃ initialLocalValues,
      let execution := (plannerInputAtEntry before entry).execute initialLocalValues
      execution.1 = .assertionExit ∧ after.state = execution.2 ∧
      resultMatchesModel (plannerInputAtEntry before entry) execution

/-- Execute the real method with an arbitrary caller return address.
Normal return preserves the callee-saved registers. Assertion failure transfers control
to external `exit` with its argument register set to 1. The implementation of
external `exit` is outside this contract. -/
def PlannerCallExecution [Host] [FunDecls] (precondition : MachineData → Prop)
    (normalReturn assertionExit : MachineData → MachineData → Prop) : Prop :=
  ∀ entry returnAddress,
    ⦃ fun current => current = entry.pushRa returnAddress ∧ precondition entry ⦄ plannerRunAsm
    ⦃ (fun _ _ => False); fun address finished =>
      (address = returnAddress ∧ normalReturn entry finished ∧ mod.Agree entry finished) ∨
      (address = label "exit" ∧ finished.regs.get64 .rdi = 1#64 ∧ assertionExit entry finished) ⦄

/-- The same method returns to the caller with success or a blocked result.
There is no assertion-exit branch in this contract. -/
def PlannerCallNormalReturnExecution [Host] [FunDecls] (precondition : MachineData → Prop)
    (normalReturn : MachineData → MachineData → Prop) : Prop :=
  ∀ entry returnAddress,
    ⦃ fun current => current = entry.pushRa returnAddress ∧ precondition entry ⦄ plannerRunAsm
    ⦃ (fun _ _ => False); fun address finished =>
      address = returnAddress ∧ normalReturn entry finished ∧ mod.Agree entry finished ⦄

/-- The call contract in any host with the generated methods and exit boundary. -/
public def PlannerAssemblyContract (inputAssumptions : PlannerInput → Prop)
    (resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop) : Prop :=
  ∀ [Host] (linkedMethods : Linked) (_exitBoundary : ExitBoundary),
    letI := linkedMethods.plannerDecls
    ∀ (plannerAddress : Addr) (initialMemory : PlannerCallMemory) (frame : MProp 64),
      PlannerCallExecution
        (PlannerCallPrecondition inputAssumptions plannerAddress initialMemory frame)
        (PlannerNormalReturn resultMatchesModel plannerAddress initialMemory frame)
        (PlannerAssertionExit resultMatchesModel plannerAddress initialMemory frame)

/-- The same call contract in the host obtained from the recorded binary layout.
Instruction and layout checks connect that record to the compiled method bytes. -/
public def PlannerBinaryContract (inputAssumptions : PlannerInput → Prop)
    (resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop) : Prop :=
  letI := binLinked.plannerDecls
  ∀ (plannerAddress : Addr) (initialMemory : PlannerCallMemory) (frame : MProp 64),
    PlannerCallExecution
      (PlannerCallPrecondition inputAssumptions plannerAddress initialMemory frame)
      (PlannerNormalReturn resultMatchesModel plannerAddress initialMemory frame)
      (PlannerAssertionExit resultMatchesModel plannerAddress initialMemory frame)

/-- The normal-return contract in any host with the generated methods and exit boundary. -/
public def PlannerAssemblyNormalReturnContract (inputAssumptions : PlannerInput → Prop)
    (resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop) : Prop :=
  ∀ [Host] (linkedMethods : Linked) (_exitBoundary : ExitBoundary),
    letI := linkedMethods.plannerDecls
    ∀ (plannerAddress : Addr) (initialMemory : PlannerCallMemory) (frame : MProp 64),
      PlannerCallNormalReturnExecution
        (PlannerCallPrecondition inputAssumptions plannerAddress initialMemory frame)
        (PlannerNormalReturn resultMatchesModel plannerAddress initialMemory frame)

/-- The same normal-return contract in the host from the recorded binary layout. -/
public def PlannerBinaryNormalReturnContract (inputAssumptions : PlannerInput → Prop)
    (resultMatchesModel : PlannerInput → PlannerExecutionResult → Prop) : Prop :=
  letI := binLinked.plannerDecls
  ∀ (plannerAddress : Addr) (initialMemory : PlannerCallMemory) (frame : MProp 64),
    PlannerCallNormalReturnExecution
      (PlannerCallPrecondition inputAssumptions plannerAddress initialMemory frame)
      (PlannerNormalReturn resultMatchesModel plannerAddress initialMemory frame)

/-! ## Connect the contract to the instruction proof -/

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
    exact ⟨pre.rdi, pre.ok.planner.sourceSizeFitsBuffer, pre.ok.planner.targetSizeFitsBuffer,
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
  obtain ⟨after, ⟨locals, returnByte, finalState, objectFields, dataAddress,
    operationsAddress, sourcesAddress, countAddress, spillCount, count⟩,
    valid, owned⟩ := post
  change some (al returned) = code ((plannerInputAtEntry before entry).execute locals).1 at returnByte
  have modelOutcomeIsNormal :
      ((plannerInputAtEntry before entry).execute locals).1 ≠ .assertionExit := by
    intro failed
    rw [failed] at returnByte
    simp only [code, reduceCtorEq] at returnByte
  exact ⟨after, valid, owned,
    ⟨objectFields, dataAddress, operationsAddress, sourcesAddress, countAddress, spillCount⟩,
    locals, returnByte, modelOutcomeIsNormal, finalState, count, comparison locals⟩

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
      (input.execute initialLocalValues).1 ≠ .assertionExit) :
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
      (input.execute initialLocalValues).1 ≠ .assertionExit) :
    PlannerBinaryNormalReturnContract inputAssumptions resultMatchesModel :=
  planner_assembly_satisfies_normal_return_contract comparison doesNotAssert binLinked binBoundary

end ShufflerVerification
