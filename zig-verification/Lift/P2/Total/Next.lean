module

public import Lift.P2.Total.Machine

@[expose] public section

namespace Lift.P2.Total

/-- A property of every completed next state under the CPU/RAM handler.
Faults have no next state. Undefined responses remain universally quantified. -/
def AllNext (post : MachineState → Prop) : Effects → Prop
  | .done state => post state
  | @Effects.undefined A support next => ∀ value, AllNext post (next value)
  | .require_read_access _ _ next => AllNext post (next ())
  | .require_write_access _ _ next => AllNext post (next ())
  | .require_exec_access _ next => AllNext post (next ())
  | .fault _ | .gp_unaligned _ _ | .unimplemented _ => True
  | .nonmem_load _ _ _ _ | .nonmem_store _ _ _ _ => True

theorem AllNext.sound {M : Type} (post : MachineState → Prop)
    (policy : CpuPolicy) (visible : DataMem → M) (prior : DataMem)
    (effect : Effects) (state : MachineState)
    (all : AllNext post effect)
    (handled : Handled policy visible prior effect (.next state)) : post state := by
  induction effect with
  | done current => cases handled; exact all
  | fault tag => cases handled
  | gp_unaligned address bytes => cases handled
  | unimplemented message => cases handled
  | nonmem_load memory address width next ih => cases handled
  | nonmem_store memory address value next ih => cases handled
  | undefined next ih =>
    cases handled with
    | choice value handled => exact ih value (all value) handled
  | require_read_access address width next ih =>
    cases handled with
    | readAllow access handled => exact ih () all handled
  | require_write_access address width next ih =>
    cases handled with
    | writeAllow access handled => exact ih () all handled
  | require_exec_access range next ih =>
    cases handled with
    | execAllow access handled => exact ih () all handled

/-- Prove a next-state property before deciding whether the RAM load succeeds. -/
theorem AllNext.load (post : MachineState → Prop) (data : MachineData)
    (address : BitVec 64) (width : Width)
    (next : width.type → MachineData → Effects)
    (all : ∀ value, AllNext post (next value data)) :
    AllNext post (data.load address width next) := by
  simp only [MachineData.load, AllNext]
  split
  · exact all _
  · trivial

/-- Store failure also has no next state; successful bytes stay exact. -/
theorem AllNext.store (post : MachineState → Prop) (data : MachineData)
    (address : BitVec 64) (width : Width) (value : width.type)
    (next : MachineData → Effects)
    (all : AllNext post (next { data with
      dmem := Mem.storeInt data.dmem address width.bytes value.toInt })) :
    AllNext post (data.store address value next) := by
  simp only [MachineData.store, AllNext]
  split
  · exact all
  · trivial

end Lift.P2.Total
