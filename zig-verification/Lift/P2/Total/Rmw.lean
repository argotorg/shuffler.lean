module

public import Lift.P2.Total.Memory

@[expose] public section

namespace Lift.P2.Total

/-- A read followed by a write at the same address. The old value remains
available to the continuation. Failures retain the exact access tag and RAM. -/
def modifyRam (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64)
    (width : Width) (update : width.type → width.type) :
    RamResult (width.type × DataMem) :=
  match readRam policy memory address width with
  | .error failure => .error failure
  | .ok old =>
    match writeRam policy memory address width (update old) with
    | .error failure => .error failure
    | .ok memory => .ok (old, memory)

/-- This operation keeps Kraken's read-before-write access order. The `prior`
argument for the final continuation is the initial instruction RAM, as in
`Handled`; this theorem does not infer RAM erased by a continuation. -/
theorem modifyRam_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width)
    (update : width.type → width.type) (k : width.type → MachineData → Effects)
    (result : StepResult M) :
    Handled policy visible data.dmem
      (data.load address width (fun old data => data.store address (update old) (k old))) result ↔
      match modifyRam policy data.dmem address width update with
      | .ok (old, memory) =>
          Handled policy visible data.dmem (k old { data with dmem := memory }) result
      | .error (reason, memory) => result = .failure reason (visible memory) := by
  rw [readRam_correct]
  cases read : readRam policy data.dmem address width with
  | error failure =>
    obtain ⟨reason, memory⟩ := failure
    simp only [modifyRam, read]
  | ok old =>
    simp only [modifyRam, read]
    rw [writeRam_correct]
    cases write : writeRam policy data.dmem address width (update old) with
    | error failure => obtain ⟨reason, memory⟩ := failure; rfl
    | ok memory => rfl

end Lift.P2.Total
