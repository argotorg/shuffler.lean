module

public import Lift.P2.Total.FiniteCmd
public import Lift.P2.Total.ControlRules
public import Lift.P2.Total.ProjectionRules
public meta import Lean
public meta import Lift.P2.Total.CheckedCmd

@[expose] public section

namespace Lift.P2.Total.StackConstant

structure Pattern where
  pushPC : Int64
  popPC : Int64
  retPC : Int64
  endPC : Int64

def returnPC (word : Int) : Int64 := Int64.ofBitVec (BitVec.ofInt 64 word)

def boundary (word : Int) : Boundary (BitVec 64) DataMem where
  returned _ final := if final.pc = returnPC word then some final.data.regs.rax.toBitVec else none
  visible initial memory := hideRam (stackScratch initial.data.regs.rsp.toBitVec) memory

/-- The only data resources are the exact eight-byte scratch and return slots.
No data pointer, scalar bound, or larger frame is assumed. -/
structure ValidCall (pattern : Pattern) (policy : CpuPolicy) (word : Int)
    (initial : MachineState) : Prop where
  pc : initial.pc = pattern.pushPC
  scratchMapped : Mem.loadInt initial.data.dmem (initial.data.regs.rsp.toBitVec - 8#64) 8 ≠ none
  scratchWrite : policy.permits (.write (initial.data.regs.rsp.toBitVec - 8#64) .W64) = true
  scratchRead : policy.permits (.read (initial.data.regs.rsp.toBitVec - 8#64) .W64) = true
  returnSlot : Mem.loadInt initial.data.dmem initial.data.regs.rsp.toBitVec 8 = some word
  returnRead : policy.permits (.read initial.data.regs.rsp.toBitVec .W64) = true
  pushAccess : policy.permits (.execute pattern.pushPC pattern.popPC) = true
  popAccess : policy.permits (.execute pattern.popPC pattern.retPC) = true
  retAccess : policy.permits (.execute pattern.retPC pattern.endPC) = true
  outsidePush : returnPC word ≠ pattern.pushPC
  outsidePop : returnPC word ≠ pattern.popPC
  outsideRet : returnPC word ≠ pattern.retPC

end Lift.P2.Total.StackConstant

public meta section

open Lean Elab Command

namespace Lift.P2.Total

/-- Generate a projected-RAM call proof for a no-argument push/pop constant.
The final theorem targets the supplied generated program and uses #p2_finite. -/
elab "#p2_stack_constant " asm:ident " step " machineStep:ident " exact " exactProof:ident
    " using " "(" program:ident "," root:term "," enter:ident ")"
    " sites " "(" pushPC:num "," popPC:num "," retPC:num "," endPC:num ")"
    " unfold " "[" extra:ident,* "]" " as " output:ident : command => do
  let patternName := mkIdent (output.getId ++ `pattern)
  let contractName := mkIdent (output.getId ++ `contract)
  let boundaryName := mkIdent (output.getId ++ `boundary)
  let modelName := mkIdent (output.getId ++ `model)
  let asTerm := fun (number : TSyntax `num) => (⟨number.raw⟩ : TSyntax `term)
  let pushTerm := asTerm pushPC
  let popTerm := asTerm popPC
  let retTerm := asTerm retPC
  let endTerm := asTerm endPC
  let patternCommand ← `(def $patternName : Lift.P2.Total.StackConstant.Pattern :=
    ⟨$pushTerm, $popTerm, $retTerm, $endTerm⟩)
  let contractCommand ← `(def $contractName :
      Lift.P2.Total.CpuPolicy → Int → MachineState → Prop :=
    Lift.P2.Total.StackConstant.ValidCall $patternName)
  let boundaryCommand ← `(def $boundaryName := Lift.P2.Total.StackConstant.boundary)
  let modelCommand ← `(def $modelName (policy : Lift.P2.Total.CpuPolicy) :
      Lift.P2.Total.Model (Lift.P2.Total.Config ($program policy) $root) (BitVec 64) DataMem where
    system := ($program policy).system $root
    «entry» initial := .running $root
      ($enter {} (Lift.P2.Total.hideRam
        (Lift.P2.Total.stackScratch initial.data.regs.rsp.toBitVec) initial.data.dmem)) .root)
  let rules := extra.getElems ++ #[patternName, boundaryName, modelName, program, enter]
  let proofCommand ← `(#p2_finite $asm step $machineStep exact $exactProof
    using ($boundaryName, $contractName, $modelName)
    depths (4, 3) sites [$pushPC, $popPC, $retPC]
    unfold [Lift.P2.Total.StackConstant.boundary, Lift.P2.Total.StackConstant.returnPC,
      Lift.P2.Total.Program.system, Lift.P2.Total.transition_iff_successors,
      Lift.P2.Total.successors, Lift.P2.Total.transition_returned, Lift.P2.Total.transition_failed,
      Lift.P2.Total.writeRam_mapped, Lift.P2.Total.readRam_storeInt64,
      Lift.P2.Total.stackScratch_preserves_return, Lift.P2.Total.stackScratch_hide_store,
      Width.bytesv, Width.bytes, UInt64.toBitVec_sub, UInt64.sub_add_cancel, $rules,*] as $output)
  generateChecked #[patternCommand, contractCommand, boundaryCommand, modelCommand, proofCommand]
    #[((← getCurrNamespace) ++ output.getId ++ `spec)]

end Lift.P2.Total
