module

public import Lift.P2.Total.MachineOrder

@[expose] public section

namespace Lift.P2.Total

/-- A logical memory update whose value is independent of the loaded bits.
The read and the undefined AF response remain part of the instruction. -/
def logicalConstantResult {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (address : BitVec 64) (width : Width)
    (value : width.type) (result : StepResult M) : Prop :=
  if policy.permits (.execute pc nextPC) then
    match modifyRam policy data.dmem address width (fun _ => value) with
    | .error (reason, memory) => result = .failure reason (visible memory)
    | .ok (_, memory) => ∃ af : Bool, result = .next
        ⟨{ data with
            dmem := memory
            status := StatusFlags.from_result value
              { cf := false, af := af, of := false } }, nextPC⟩
  else result = .failure (.denied (.execute pc nextPC)) (visible data.dmem)

theorem logicalConstantEffects_correct {M : Type} (policy : CpuPolicy)
    (visible : DataMem → M) (data : MachineData) (pc nextPC : Int64)
    (address : BitVec 64) (width : Width) (value : width.type)
    (result : StepResult M) :
    Handled policy visible data.dmem
      (.require_exec_access (pc...nextPC) (fun _ =>
        data.load address width (fun _ loaded =>
          .undefined (fun af : Bool =>
            { loaded with
              status := StatusFlags.from_result value
                { cf := false, af := af, of := false } }.store address value
              (fun stored => .done ⟨stored, nextPC⟩))))) result ↔
      logicalConstantResult policy visible data pc nextPC address width value result := by
  simp only [Handled.exec_all_iff, logicalConstantResult]
  split
  · simp only [readRam_correct]
    cases read : readRam policy data.dmem address width with
    | error failure =>
      obtain ⟨reason, memory⟩ := failure
      simp [modifyRam, read]
    | ok old =>
      simp only [modifyRam, read, Handled.choice_iff,
        Handled.store_normalize, Handled.done_iff]
      cases write : writeRam policy data.dmem address width value with
      | error failure =>
        obtain ⟨reason, memory⟩ := failure
        simp
      | ok memory => simp
  · rfl

-- Concrete masks also occur as numerals in exact instruction bodies.
@[simp] theorem or_ones8 (value : BitVec 8) :
    value ||| 255#8 = 255#8 := BitVec.or_allOnes

@[simp] theorem or_ones16 (value : BitVec 16) :
    value ||| 65535#16 = 65535#16 := BitVec.or_allOnes

@[simp] theorem or_ones32 (value : BitVec 32) :
    value ||| 4294967295#32 = 4294967295#32 := BitVec.or_allOnes

@[simp] theorem or_ones64 (value : BitVec 64) :
    value ||| 18446744073709551615#64 = 18446744073709551615#64 := BitVec.or_allOnes

end Lift.P2.Total
