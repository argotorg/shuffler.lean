module

public import Lift.P2.Total.Footprint

@[expose] public section

namespace Lift.P2.Total

theorem Handled.choice_iff {M A : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (support : NondetSupportingType A) (k : A → Effects)
    (result : StepResult M) :
    Handled policy visible prior (@Effects.undefined A support k) result ↔
      ∃ value, Handled policy visible prior (k value) result := by
  constructor
  · intro h; cases h with | choice value next => exact ⟨value, next⟩
  · rintro ⟨value, next⟩; exact .choice value next

/-- A choice can be removed only when every response has the same continuation. -/
@[simp] theorem Handled.choice_const_iff {M A : Type} (policy : CpuPolicy)
    (visible : DataMem → M) (prior : DataMem) (support : NondetSupportingType A)
    (e : Effects) (result : StepResult M) :
    Handled policy visible prior (@Effects.undefined A support (fun _ => e)) result ↔
      Handled policy visible prior e result := by
  rw [Handled.choice_iff]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨@NondetSupportingType.from_hash A support 0, h⟩

theorem Handled.load_next_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width)
    (k : width.type → MachineData → MachineState) (t : MachineState) :
    Handled policy visible data.dmem (data.load address width (fun v d => .done (k v d))) (.next t) ↔
      ∃ value, readRam policy data.dmem address width = .ok value ∧ t = k value data := by
  rw [readRam_correct]
  cases h : readRam policy data.dmem address width with
  | ok value => simp
  | error failure => obtain ⟨reason, memory⟩ := failure; simp

theorem Handled.load_failure_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width)
    (k : width.type → MachineData → MachineState) (reason : Failure) (memory : M) :
    Handled policy visible data.dmem (data.load address width (fun v d => .done (k v d)))
      (.failure reason memory) ↔
      ∃ ram, readRam policy data.dmem address width = .error (reason, ram) ∧ memory = visible ram := by
  rw [readRam_correct]
  cases h : readRam policy data.dmem address width with
  | ok value => simp
  | error failure =>
    obtain ⟨tag, ram⟩ := failure
    simp only [Handled.done_iff, reduceCtorEq, Except.error.injEq, Prod.mk.injEq,
      StepResult.failure.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨ram, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨ram2, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩

theorem Handled.store_next_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width) (value : width.type)
    (k : MachineData → MachineState) (t : MachineState) :
    Handled policy visible data.dmem (data.store address value (fun d => .done (k d))) (.next t) ↔
      ∃ memory, writeRam policy data.dmem address width value = .ok memory ∧
        t = k { data with dmem := memory } := by
  rw [writeRam_correct]
  cases h : writeRam policy data.dmem address width value with
  | ok memory => simp
  | error failure => obtain ⟨reason, memory⟩ := failure; simp

theorem Handled.store_failure_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (data : MachineData) (address : BitVec 64) (width : Width) (value : width.type)
    (k : MachineData → MachineState) (reason : Failure) (memory : M) :
    Handled policy visible data.dmem (data.store address value (fun d => .done (k d)))
      (.failure reason memory) ↔
      ∃ ram, writeRam policy data.dmem address width value = .error (reason, ram) ∧ memory = visible ram := by
  rw [writeRam_correct]
  cases h : writeRam policy data.dmem address width value with
  | ok memory => simp
  | error failure =>
    obtain ⟨tag, ram⟩ := failure
    simp only [Handled.done_iff, reduceCtorEq, Except.error.injEq, Prod.mk.injEq,
      StepResult.failure.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨ram, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨ram2, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩

end Lift.P2.Total
