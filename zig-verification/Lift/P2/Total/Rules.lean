module

public import Lift.P2.Total.Spec

@[expose] public section

namespace Lift.P2.Total

@[simp] theorem Handled.done_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (s : MachineState) (result : StepResult M) :
    Handled policy visible prior (.done s) result ↔ result = .next s := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst result; exact .done s

@[simp] theorem Handled.fault_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (tag : Fault) (result : StepResult M) :
    Handled policy visible prior (.fault tag) result ↔
      result = .failure (.processor tag) (visible prior) := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst result; exact .fault tag

theorem Handled.exec_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (p : Std.Rco Int64) (k : Unit → Effects) (result : StepResult M)
    (allow : policy.permits (.execute p.lower p.upper) = true) :
    Handled policy visible prior (.require_exec_access p k) result ↔
      Handled policy visible prior (k ()) result := by
  constructor
  · intro h
    cases h with
    | execAllow _ h => exact h
    | execDeny denied => simp [allow] at denied
  · exact .execAllow allow

theorem Handled.read_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (a : BitVec 64) (w : Width) (k : Unit → Effects) (result : StepResult M)
    (allow : policy.permits (.read a w) = true) :
    Handled policy visible prior (.require_read_access a w k) result ↔
      Handled policy visible prior (k ()) result := by
  constructor
  · intro h
    cases h with
    | readAllow _ h => exact h
    | readDeny denied => simp [allow] at denied
  · exact .readAllow allow

theorem Handled.write_iff {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (a : BitVec 64) (w : Width) (k : Unit → Effects) (result : StepResult M)
    (allow : policy.permits (.write a w) = true) :
    Handled policy visible prior (.require_write_access a w k) result ↔
      Handled policy visible prior (k ()) result := by
  constructor
  · intro h
    cases h with
    | writeAllow _ h => exact h
    | writeDeny denied => simp [allow] at denied
  · exact .writeAllow allow

end Lift.P2.Total
