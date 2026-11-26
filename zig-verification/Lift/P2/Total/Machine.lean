module

public import Lift.P2.Total.System
public import Lift.P1.Execution

@[expose] public section

namespace Lift.P2.Total

inductive Access where
  | read (address : BitVec 64) (width : Width)
  | write (address : BitVec 64) (width : Width)
  | execute (lower upper : Int64)

/-- The fixed CPU/RAM policy. No device services an access outside DataMem. -/
structure CpuPolicy where
  permits : Access → Bool

inductive Failure where
  | processor (tag : Fault)
  | unaligned (address : BitVec 64) (bytes : Nat)
  | denied (request : Access)
  | unmappedRead (address : BitVec 64) (width : Width)
  | unmappedWrite (address : BitVec 64) (width : Width) (value : width.type)
  | unsupported (message : String)

inductive Outcome (V M : Type) where
  | returned (value : V) (memory : M)
  | failure (reason : Failure) (memory : M)

inductive StepResult (M : Type) where
  | next (state : MachineState)
  | failure (reason : Failure) (memory : M)

/-- Interpret one finite Effects tree. Undefined responses remain relational.
For a fault without RAM in its payload, preserve the last completed prefix's RAM. -/
inductive Handled {M : Type} (policy : CpuPolicy) (visible : DataMem → M) (prior : DataMem) :
    Effects → StepResult M → Prop where
  | done (s : MachineState) : Handled policy visible prior (.done s) (.next s)
  | fault (tag : Fault) :
      Handled policy visible prior (.fault tag) (.failure (.processor tag) (visible prior))
  | unaligned (address : BitVec 64) (bytes : Nat) :
      Handled policy visible prior (.gp_unaligned address bytes)
        (.failure (.unaligned address bytes) (visible prior))
  | unsupported (message : String) :
      Handled policy visible prior (.unimplemented message)
        (.failure (.unsupported message) (visible prior))
  | unmappedRead (m : DataMem) (a : BitVec 64) (w : Width) (k : w.type → DataMem → Effects) :
      Handled policy visible prior (.nonmem_load m a w k)
        (.failure (.unmappedRead a w) (visible m))
  | unmappedWrite (m : DataMem) (a : BitVec 64) (w : Width) (v : w.type) (k : DataMem → Effects) :
      Handled policy visible prior (.nonmem_store m a v k)
        (.failure (.unmappedWrite a w v) (visible m))
  | choice {A : Type} {support : NondetSupportingType A} {k : A → Effects}
      (value : A) {result : StepResult M}
      (next : Handled policy visible prior (k value) result) :
      Handled policy visible prior (@Effects.undefined A support k) result
  | readAllow {a : BitVec 64} {w : Width} {k : Unit → Effects} {result : StepResult M}
      (access : policy.permits (.read a w) = true)
      (next : Handled policy visible prior (k ()) result) :
      Handled policy visible prior (.require_read_access a w k) result
  | readDeny {a : BitVec 64} {w : Width} {k : Unit → Effects}
      (access : policy.permits (.read a w) = false) :
      Handled policy visible prior (.require_read_access a w k)
        (.failure (.denied (.read a w)) (visible prior))
  | writeAllow {a : BitVec 64} {w : Width} {k : Unit → Effects} {result : StepResult M}
      (access : policy.permits (.write a w) = true)
      (next : Handled policy visible prior (k ()) result) :
      Handled policy visible prior (.require_write_access a w k) result
  | writeDeny {a : BitVec 64} {w : Width} {k : Unit → Effects}
      (access : policy.permits (.write a w) = false) :
      Handled policy visible prior (.require_write_access a w k)
        (.failure (.denied (.write a w)) (visible prior))
  | execAllow {p : Std.Rco Int64} {k : Unit → Effects} {result : StepResult M}
      (access : policy.permits (.execute p.lower p.upper) = true)
      (next : Handled policy visible prior (k ()) result) :
      Handled policy visible prior (.require_exec_access p k) result
  | execDeny {p : Std.Rco Int64} {k : Unit → Effects}
      (access : policy.permits (.execute p.lower p.upper) = false) :
      Handled policy visible prior (.require_exec_access p k)
        (.failure (.denied (.execute p.lower p.upper)) (visible prior))

theorem Handled.total {M : Type} (policy : CpuPolicy) (visible : DataMem → M)
    (prior : DataMem) (e : Effects) : ∃ result, Handled policy visible prior e result := by
  induction e with
  | done s => exact ⟨_, .done s⟩
  | fault f => exact ⟨_, .fault f⟩
  | gp_unaligned a w => exact ⟨_, .unaligned a w⟩
  | unimplemented msg => exact ⟨_, .unsupported msg⟩
  | nonmem_load m a w k _ => exact ⟨_, .unmappedRead m a w k⟩
  | nonmem_store m a v k _ => exact ⟨_, .unmappedWrite m a _ v k⟩
  | @undefined A support k ih =>
    obtain ⟨result, h⟩ := ih (@NondetSupportingType.from_hash A support 0)
    exact ⟨result, .choice _ h⟩
  | require_read_access a w k ih =>
    cases h : policy.permits (.read a w) with
    | false => exact ⟨_, .readDeny h⟩
    | true => obtain ⟨result, next⟩ := ih (); exact ⟨result, .readAllow h next⟩
  | require_write_access a w k ih =>
    cases h : policy.permits (.write a w) with
    | false => exact ⟨_, .writeDeny h⟩
    | true => obtain ⟨result, next⟩ := ih (); exact ⟨result, .writeAllow h next⟩
  | require_exec_access p k ih =>
    cases h : policy.permits (.execute p.lower p.upper) with
    | false => exact ⟨_, .execDeny h⟩
    | true => obtain ⟨result, next⟩ := ih (); exact ⟨result, .execAllow h next⟩

/-- Stop only at the specified call boundary; every other instruction retains its outcomes. -/
def cpuSystem {V M : Type} (step : MachineState → Effects) (policy : CpuPolicy)
    (returned : MachineState → Option V) (visible : DataMem → M) :
    System MachineState (Outcome V M) where
  step s t := returned s = none ∧ Handled policy visible s.data.dmem (step s) (.next t)
  stop s out :=
    (∃ value, returned s = some value ∧ out = .returned value (visible s.data.dmem)) ∨
    (returned s = none ∧ ∃ reason mem,
      Handled policy visible s.data.dmem (step s) (.failure reason mem) ∧ out = .failure reason mem)

theorem cpuSystem_of_L1Spec {V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (spec : Lift.P1.L1Spec asm step) (policy : CpuPolicy)
    (returned : MachineState → Option V) (visible : DataMem → M) :
    cpuSystem step policy returned visible =
      cpuSystem (fun s => asm.step s Effects.done) policy returned visible := by
  rw [Lift.P1.L1Spec.step_eq asm step spec]

end Lift.P2.Total
