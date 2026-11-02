module

public import Theorems.PlannerInput
import all FlatShuffler.Unit.Plan.PlannerRunDefs
import all FlatShuffler.PlannerLink
import all FlatShuffler.BinHost

/-!
# The machine claim: memory, arguments, return, and assertion exit

`PlannerCallMemory` records the native object, buffer addresses, and buffer contents.
Its `p` field records the `Planner` object; `sw` and `tw` are the source and target
words. These types and their memory views are defined in `Theorems/NativeInterface.lean`.
The conditions below expand their validity predicates.

The separation operator `∗` requires disjoint owned regions. `frame` is arbitrary
caller memory. Both postconditions preserve it. Stack storage is measured in
eight-byte words; 8240 words cover the deepest call, plus a separate return slot.
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
  sourceSizeFitsBuffer : memory.p.m.toNat ≤ MAX_N
  targetSizeFitsBuffer : memory.p.n.toNat ≤ MAX_N
  sourceBufferLength : memory.p.sw.length = memory.p.m.toNat
  targetBufferLength : memory.p.tw.length = memory.p.n.toNat
  spillByteCountFitsAddress : memory.spillCount ≤ 2 ^ 32
  sourceVariableIdsFitSpillBuffer : ∀ id ∈ splIds memory.p.sw, id < memory.spillCount
  targetVariableIdsFitSpillBuffer : ∀ id ∈ splIds memory.p.tw, id < memory.spillCount
  operationBufferLength : memory.ops.length = 6 * memory.p.n.toNat + 4 * memory.p.m.toNat
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
      al returned = code execution.1 ∧ execution.1 ≠ .assertionFailed ∧ after.state = execution.2 ∧
      after.count = (if execution.1 = .done then .ofNat 64 execution.2.trace.length
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
      execution.1 = .assertionFailed ∧ after.state = execution.2 ∧
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

end ShufflerVerification
