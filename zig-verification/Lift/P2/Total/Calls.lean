module

public import Lift.P2.Total.StackResources
public import Lift.P2.Total.Normalize
public import Lift.P2.Total.ControlRules

@[expose] public section

namespace Lift.P2.Total.Stack

def callAddress (data : MachineData) : BitVec 64 := data.regs.rsp.toBitVec - 8#64

def callState (data : MachineData) (returnPC targetPC : Int64) : MachineState :=
  ⟨{ data with
      regs := data.regs.set64 .rsp (callAddress data)
      dmem := Mem.storeInt data.dmem (callAddress data) 8 returnPC.toBitVec.toInt }, targetPC⟩

def returnState (data : MachineData) (word : BitVec 64) : MachineState :=
  ⟨{ data with regs := data.regs.set64 .rsp (data.regs.rsp.toBitVec + 8#64) },
    Int64.ofBitVec word⟩

/-- These are the exact direct-call effects, including the stack write. -/
def callEffects (data : MachineData) (pc returnPC targetPC : Int64) : Effects :=
  .require_exec_access (pc...returnPC) (fun _ =>
    { data with regs := data.regs.set64 .rsp (callAddress data) }.store
      (callAddress data) (w := .W64) returnPC.toBitVec
      (fun stored => .done ⟨stored, targetPC⟩))

def returnEffects (data : MachineData) (pc nextPC : Int64) : Effects :=
  .require_exec_access (pc...nextPC) (fun _ =>
    data.load data.regs.rsp.toBitVec .W64 (fun word current =>
      .done (returnState current word)))

def callResult {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc returnPC targetPC : Int64) (result : StepResult M) : Prop :=
  if policy.permits (.execute pc returnPC) then
    match writeRam policy data.dmem (callAddress data) .W64 returnPC.toBitVec with
    | .ok memory => result = .next ⟨{ data with
        regs := data.regs.set64 .rsp (callAddress data), dmem := memory }, targetPC⟩
    | .error (reason, memory) => result = .failure reason (visible memory)
  else result = .failure (.denied (.execute pc returnPC)) (visible data.dmem)

def returnResult {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (result : StepResult M) : Prop :=
  if policy.permits (.execute pc nextPC) then
    match readRam policy data.dmem data.regs.rsp.toBitVec .W64 with
    | .ok word => result = .next (returnState data word)
    | .error (reason, memory) => result = .failure reason (visible memory)
  else result = .failure (.denied (.execute pc nextPC)) (visible data.dmem)

theorem callEffects_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc returnPC targetPC : Int64) (result : StepResult M) :
    Handled policy visible data.dmem (callEffects data pc returnPC targetPC) result ↔
      callResult policy visible data pc returnPC targetPC result := by
  simp only [callEffects, Handled.exec_all_iff, callResult]
  split
  · rw [Handled.store_normalize policy visible data.dmem
      { data with regs := data.regs.set64 .rsp (callAddress data) }
      (callAddress data) .W64 returnPC.toBitVec
      (fun stored => .done ⟨stored, targetPC⟩) result rfl]
    cases writeRam policy data.dmem (callAddress data) .W64 returnPC.toBitVec with
    | error failure => obtain ⟨reason, memory⟩ := failure; rfl
    | ok memory => exact Handled.done_iff _ _ _ _ _
  · rfl

theorem returnEffects_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (result : StepResult M) :
    Handled policy visible data.dmem (returnEffects data pc nextPC) result ↔
      returnResult policy visible data pc nextPC result := by
  simp only [returnEffects, Handled.exec_all_iff, returnResult]
  split
  · rw [readRam_correct]
    cases readRam policy data.dmem data.regs.rsp.toBitVec .W64 with
    | error failure => obtain ⟨reason, memory⟩ := failure; rfl
    | ok word => exact Handled.done_iff _ _ _ _ _
  · rfl

/-- A checked exact slot resource removes only this call's stack failure. -/
theorem call_entry {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc returnPC targetPC : Int64)
    (mapped : Mem.loadInt data.dmem (callAddress data) 8 ≠ none)
    (writeAllowed : policy.permits (.write (callAddress data) .W64) = true)
    (executeAllowed : policy.permits (.execute pc returnPC) = true)
    (result : StepResult M) :
    Handled policy visible data.dmem (callEffects data pc returnPC targetPC) result ↔
      result = .next (callState data returnPC targetPC) := by
  rw [callEffects_correct]
  simp only [callResult, executeAllowed, ↓reduceIte]
  rw [writeRam_mapped policy data.dmem (callAddress data) .W64 returnPC.toBitVec
    writeAllowed mapped]
  rfl

/-- A callee can return only after its saved word and restored RSP are checked. -/
theorem return_exit {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC returnPC : Int64)
    (word : Mem.loadInt data.dmem data.regs.rsp.toBitVec 8 = some returnPC.toBitVec.toInt)
    (readAllowed : policy.permits (.read data.regs.rsp.toBitVec .W64) = true)
    (executeAllowed : policy.permits (.execute pc nextPC) = true)
    (result : StepResult M) :
    Handled policy visible data.dmem (returnEffects data pc nextPC) result ↔
      result = .next (returnState data returnPC.toBitVec) := by
  rw [returnEffects_correct]
  simp only [returnResult, executeAllowed, ↓reduceIte]
  rw [readRam_mapped policy data.dmem data.regs.rsp.toBitVec .W64
    returnPC.toBitVec.toInt readAllowed word]
  simp only [BitVec.ofInt_toInt]

/-- The machine call writes only private bytes under the fixed call projection. -/
theorem call_entry_hidden (frame : Frame) (data : MachineData) (returnPC targetPC : Int64)
    (fits : 8 ≤ frame.bytes) :
    hideRam (frame.privateByte data.regs.rsp.toBitVec)
        (callState data returnPC targetPC).data.dmem =
      hideRam (frame.privateByte data.regs.rsp.toBitVec) data.dmem := by
  exact (Slot.mk 8 .W64 (by decide) fits).hide_store data.regs.rsp.toBitVec
    data.dmem returnPC.toBitVec.toInt

end Lift.P2.Total.Stack
