module

public import Lift.P2.Total.Machine

@[expose] public section

namespace Lift.P2.Total

/-- The return boundary and the RAM projection can depend on the initial call.
For example, the private stack interval is fixed from that call, not recomputed
from the stack pointer at each later instruction. -/
structure Boundary (V M : Type) where
  returned : MachineState → MachineState → Option V
  visible : MachineState → DataMem → M

structure Model (A V M : Type) where
  system : System A (Outcome V M)
  /-- A defined entry projection covers every admitted concrete call. -/
  entry : MachineState → A

/-- The SysV integer-register obligations at a completed call. -/
def AbiRestored (initial final : MachineState) : Prop :=
  final.data.regs.rsp = initial.data.regs.rsp + 8 ∧
  final.data.regs.rbx = initial.data.regs.rbx ∧
  final.data.regs.rbp = initial.data.regs.rbp ∧
  final.data.regs.r12 = initial.data.regs.r12 ∧
  final.data.regs.r13 = initial.data.regs.r13 ∧
  final.data.regs.r14 = initial.data.regs.r14 ∧
  final.data.regs.r15 = initial.data.regs.r15

def source {V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (initial : MachineState) : System MachineState (Outcome V M) :=
  cpuSystem (fun s => asm.step s Effects.done) policy
    (boundary.returned initial) (boundary.visible initial)

/-- Both inclusions of the behavior sets, for every call allowed by the contract.
This includes actual infinite traces and each failure with its tag and visible RAM. -/
def P2Spec {A V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M) : Prop :=
  ∀ initial, contract initial →
    Equivalent (source asm policy boundary initial) model.system initial (model.entry initial)

/-- The public call theorem also proves restoration of the ABI state that L2 hides. -/
def CallSpec {A V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M) : Prop :=
  P2Spec asm policy boundary contract model ∧
  ∀ initial, contract initial → ∀ final value,
    (source asm policy boundary initial).Reaches initial final →
    boundary.returned initial final = some value → AbiRestored initial final

theorem cpuSystem.total {V M : Type} (step : MachineState → Effects) (policy : CpuPolicy)
    (returned : MachineState → Option V) (visible : DataMem → M) (s : MachineState) :
    (∃ t, (cpuSystem step policy returned visible).step s t) ∨
      ∃ out, (cpuSystem step policy returned visible).stop s out := by
  cases hret : returned s with
  | some value => exact Or.inr ⟨.returned value (visible s.data.dmem), Or.inl ⟨value, hret, rfl⟩⟩
  | none =>
    obtain ⟨result, h⟩ := Handled.total policy visible s.data.dmem (step s)
    cases result with
    | next t => exact Or.inl ⟨t, hret, h⟩
    | failure reason mem => exact Or.inr ⟨.failure reason mem, Or.inr ⟨hret, reason, mem, h, rfl⟩⟩

theorem P2Spec.of_L1 {A V M : Type} (asm : _root_.Executable)
    (step : MachineState → Effects) (spec : Lift.P1.L1Spec asm step) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M)
    (proof : ∀ initial, contract initial →
      Equivalent (cpuSystem step policy (boundary.returned initial) (boundary.visible initial))
        model.system initial (model.entry initial)) :
    P2Spec asm policy boundary contract model := by
  intro initial valid
  have result := proof initial valid
  rw [cpuSystem_of_L1Spec asm step spec] at result
  exact result

theorem P2Spec.of_bisimulation {A V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M)
    (relation : MachineState → MachineState → A → Prop)
    (proof : ∀ initial, contract initial →
      Bisimulation (source asm policy boundary initial) model.system (relation initial))
    (entry : ∀ initial, contract initial → relation initial initial (model.entry initial)) :
    P2Spec asm policy boundary contract model :=
  fun initial valid => (proof initial valid).equivalent (entry initial valid)

theorem CallSpec.of_bisimulation {A V M : Type} (asm : _root_.Executable) (policy : CpuPolicy)
    (boundary : Boundary V M) (contract : MachineState → Prop) (model : Model A V M)
    (relation : MachineState → MachineState → A → Prop)
    (proof : ∀ initial, contract initial →
      Bisimulation (source asm policy boundary initial) model.system (relation initial))
    (entry : ∀ initial, contract initial → relation initial initial (model.entry initial))
    (exit : ∀ initial, contract initial → ∀ final a value,
      relation initial final a → boundary.returned initial final = some value → AbiRestored initial final) :
    CallSpec asm policy boundary contract model := by
  refine ⟨P2Spec.of_bisimulation asm policy boundary contract model relation proof entry, ?_⟩
  intro initial valid final value path returned
  obtain ⟨a, _, related⟩ := (proof initial valid).forward.reaches (entry initial valid) path
  exact exit initial valid final a value related returned

end Lift.P2.Total
