module

public import Lift.P2.Total.Rules

@[expose] public section

namespace Lift.P2.Total

/-- Failure keeps the RAM at the access point. There is no Option/fuel failure. -/
abbrev RamResult (A : Type) := Except (Failure × DataMem) A

def readRam (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64) (width : Width) :
    RamResult width.type :=
  if policy.permits (.read address width) then
    match Mem.loadInt memory address width.bytes with
    | some value => .ok (BitVec.ofInt width.bits value)
    | none => .error (.unmappedRead address width, memory)
  else .error (.denied (.read address width), memory)

def writeRam (policy : CpuPolicy) (memory : DataMem) (address : BitVec 64)
    (width : Width) (value : width.type) : RamResult DataMem :=
  if policy.permits (.write address width) then
    match Mem.loadInt memory address width.bytes with
    | some _ => .ok (Mem.storeInt memory address width.bytes value.toInt)
    | none => .error (.unmappedWrite address width value, memory)
  else .error (.denied (.write address width), memory)

/-- The L2 read has the same permitted and failed accesses as Kraken's primitive. -/
theorem readRam_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width)
    (k : width.type → MachineData → Effects) (result : StepResult M) :
    Handled policy visible data.dmem (data.load address width k) result ↔
      match readRam policy data.dmem address width with
      | .ok value => Handled policy visible data.dmem (k value data) result
      | .error (reason, memory) => result = .failure reason (visible memory) := by
  cases allow : policy.permits (.read address width) with
  | false =>
    simp only [readRam, allow, Bool.false_eq_true, ↓reduceIte, MachineData.load]
    constructor
    · intro h
      cases h with
      | readAllow permitted _ => simp [allow] at permitted
      | readDeny _ => rfl
    · intro h; subst result; exact .readDeny allow
  | true =>
    simp only [readRam, allow, ↓reduceIte, MachineData.load]
    rw [Handled.read_iff _ _ _ _ _ _ _ allow]
    cases loaded : Mem.loadInt data.dmem address width.bytes with
    | some value => simp only [loaded]
    | none =>
      simp only [loaded]
      constructor
      · intro h; cases h; rfl
      · intro h; subst result; exact .unmappedRead _ _ _ _

/-- Stores update existing mapped bytes, as Kraken does; they do not allocate RAM. -/
theorem writeRam_correct {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width) (value : width.type)
    (k : MachineData → Effects) (result : StepResult M) :
    Handled policy visible data.dmem (data.store address value k) result ↔
      match writeRam policy data.dmem address width value with
      | .ok memory => Handled policy visible data.dmem (k { data with dmem := memory }) result
      | .error (reason, memory) => result = .failure reason (visible memory) := by
  cases allow : policy.permits (.write address width) with
  | false =>
    simp only [writeRam, allow, Bool.false_eq_true, ↓reduceIte, MachineData.store]
    constructor
    · intro h
      cases h with
      | writeAllow permitted _ => simp [allow] at permitted
      | writeDeny _ => rfl
    · intro h; subst result; exact .writeDeny allow
  | true =>
    simp only [writeRam, allow, ↓reduceIte, MachineData.store]
    rw [Handled.write_iff _ _ _ _ _ _ _ allow]
    cases loaded : Mem.loadInt data.dmem address width.bytes with
    | some old => simp only [loaded]
    | none =>
      simp only [loaded]
      constructor
      · intro h; cases h; rfl
      · intro h; subst result; exact .unmappedWrite _ _ _ _ _

end Lift.P2.Total
