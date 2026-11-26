module

public import Lift.P2.Total.Rmw
public import Lift.P2.Total.Normalize

@[expose] public section

namespace Lift.P2.Total

/-- Full instruction outcomes for AND-zero. Execution denial, read failure,
write failure, and every undefined AF response remain observable. -/
def andZeroResult {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (address : BitVec 64) (width : Width)
    (result : StepResult M) : Prop :=
  if policy.permits (.execute pc nextPC) then
    match modifyRam policy data.dmem address width (fun _ => 0) with
    | .error (reason, memory) => result = .failure reason (visible memory)
    | .ok (_, memory) => ∃ af : Bool, result = .next
        ⟨{ data with
            dmem := memory
            status := StatusFlags.from_result (0 : width.type)
              { cf := false, af := af, of := false } }, nextPC⟩
  else result = .failure (.denied (.execute pc nextPC)) (visible data.dmem)

/-- The undefined flag choice occurs between the read and write in Kraken.
It can move past the write result because it does not change that access. -/
theorem andZeroEffects_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (address : BitVec 64) (width : Width)
    (result : StepResult M) :
    Handled policy visible data.dmem
      (.require_exec_access (pc...nextPC) (fun _ =>
        data.load address width (fun _ loaded =>
          .undefined (fun af : Bool =>
            { loaded with
              status := StatusFlags.from_result (0 : width.type)
                { cf := false, af := af, of := false } }.store address (0 : width.type)
              (fun stored => .done ⟨stored, nextPC⟩))))) result ↔
      andZeroResult policy visible data pc nextPC address width result := by
  simp only [Handled.exec_all_iff, andZeroResult]
  split
  · simp only [readRam_correct]
    cases read : readRam policy data.dmem address width with
    | error failure =>
      obtain ⟨reason, memory⟩ := failure
      simp [modifyRam, read]
    | ok old =>
      simp only [modifyRam, read, Handled.choice_iff,
        Handled.store_normalize, Handled.done_iff]
      cases write : writeRam policy data.dmem address width 0 with
      | error failure =>
        obtain ⟨reason, memory⟩ := failure
        simp
      | ok memory => simp
  · rfl

/-- Exact outcomes for one CPU/RAM load, with a supplied register update. -/
def loadResult {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (address : BitVec 64) (width : Width)
    (finish : width.type → MachineData → MachineState) (result : StepResult M) : Prop :=
  if policy.permits (.execute pc nextPC) then
    match readRam policy data.dmem address width with
    | .error (reason, memory) => result = .failure reason (visible memory)
    | .ok loaded => result = .next (finish loaded data)
  else result = .failure (.denied (.execute pc nextPC)) (visible data.dmem)

theorem loadEffects_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (pc nextPC : Int64) (address : BitVec 64) (width : Width)
    (finish : width.type → MachineData → MachineState) (result : StepResult M) :
    Handled policy visible data.dmem
      (.require_exec_access (pc...nextPC) (fun _ =>
        data.load address width (fun loaded current => .done (finish loaded current)))) result ↔
      loadResult policy visible data pc nextPC address width finish result := by
  simp only [Handled.exec_all_iff, loadResult]
  split
  · rw [readRam_correct]
    cases readRam policy data.dmem address width with
    | error failure => obtain ⟨reason, memory⟩ := failure; rfl
    | ok loaded => exact Handled.done_iff _ _ _ _ _
  · rfl

end Lift.P2.Total
