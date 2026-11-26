module

public import Lift.Spike.Sites
public import Lift.Spike.L1

@[expose] public section

/-! Helpers for the block lemmas of `toyTwo` and `toyJob` (`Lift/Spike/Sites/Two.lean`,
`Job.lean`): `pushq`, `callq`, the end of a step with one load or one store, and facts on
memory after a write.

The flags: a block lemma takes its postcondition for each value of the flags at the exit
(`∀ f : StatusFlags, Q ⟨{ d with regs := …, dmem := …, status := f }, pc⟩`). No instruction of the
toys reads a flag that an earlier block sets, so a later proof never reasons on flag values. -/

namespace Lift.Spike.Sites.Stack

open Lift.P2.Total Lift.Sem

/-- A permitted load of the value `v`, whose continuation ends the step. -/
theorem load_done_iff {policy : CpuPolicy} (d : MachineData) (a : BitVec 64) (w : Width)
    (k : w.type → MachineData → MachineState) {v : w.type}
    (h : readRam policy d.dmem a w = .ok v) (r : StepResult DataMem) :
    Handled policy id d.dmem (d.load a w fun v s => .done (k v s)) r ↔ r = .next (k v d) := by
  rw [Sites.load_iff _ _ _ _ _ _ h, Handled.done_iff]

/-- A permitted store to mapped memory that gives the memory `m`, whose continuation ends the
step. -/
theorem store_done_iff {policy : CpuPolicy} (d : MachineData) (a : BitVec 64) {w : Width}
    (v : w.type) (k : MachineData → MachineState) {m : DataMem}
    (h : writeRam policy d.dmem a w v = .ok m) (r : StepResult DataMem) :
    Handled policy id d.dmem (d.store a v fun s => .done (k s)) r ↔
      r = .next (k { d with dmem := m }) := by
  rw [writeRam_correct, h]
  exact Handled.done_iff _ _ _ _ _

/-- The effect of `pushq` of `v` after its execute check; `pc` is the next instruction. -/
def push (d : MachineData) (v : BitVec 64) (pc : Int64) : Effects :=
  d.store (d.regs.rsp.toBitVec - 8) v fun s =>
    .done ⟨{ s with regs := { s.regs with rsp := d.regs.rsp - 8 } }, pc⟩

/-- `pushq` of `v` with a permitted write that gives the memory `m`. -/
theorem push_iff {policy : CpuPolicy} (d : MachineData) (v : BitVec 64) (pc : Int64) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 v = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (push d v pc) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp - 8 }, dmem := m }, pc⟩ := by
  rw [push, store_done_iff _ _ _ _ h]

/-- The effect of `callq` to `target` after its execute check; `ra` is the next instruction. -/
def call (d : MachineData) (ra target : Int64) : Effects :=
  { d with regs := { d.regs with rsp := d.regs.rsp - 8 } }.store (d.regs.rsp.toBitVec - 8)
    ra.toBitVec fun s => .done ⟨s, target⟩

/-- `callq` with a permitted write of the return address `ra` that gives the memory `m`. -/
theorem call_iff {policy : CpuPolicy} (d : MachineData) (ra target : Int64) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 ra.toBitVec = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (call d ra target) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp - 8 }, dmem := m }, target⟩ := by
  exact store_done_iff { d with regs := { d.regs with rsp := d.regs.rsp - 8 } } _ _ _ h r

/-- A successful write gives the memory with the bytes of `v` at `a` (a copy of
`writeRam_memory` of `Lift.P2.Total.Normalize`, which this file does not import). -/
theorem writeRam_eq {policy : CpuPolicy} {m m' : DataMem} {a : BitVec 64} {w : Width} {v : w.type}
    (h : writeRam policy m a w v = .ok m') : m' = Mem.storeInt m a w.bytes v.toInt := by
  unfold writeRam at h
  split at h
  · split at h
    · exact (Except.ok.inj h).symm
    · cases h
  · cases h

/-- A write of `v` at `a` that gives `m'`: a permitted read of `a` in `m'` gives `v`. -/
theorem readRam_writeRam {policy : CpuPolicy} {m m' : DataMem} {a v : BitVec 64}
    (h : writeRam policy m a .W64 v = .ok m') (hr : policy.permits (.read a .W64) = true) :
    readRam policy m' a .W64 = .ok v := by
  rw [writeRam_eq h]
  simp [readRam, hr, Width.bytes, Width.bits, Mem.loadInt_storeInt_64,
    BitVec.ofInt_ofBytes_toBytes_64]

/-- A write of `ra` at the stack pointer of `t` that gives the memory of `t`: `ra` is the
return address of `t`. -/
theorem retAddr_writeRam {policy : CpuPolicy} {m : DataMem} {t : MachineState} {ra : Int64}
    (h : writeRam policy m t.data.regs.rsp.toBitVec .W64 ra.toBitVec = .ok t.data.dmem) :
    SysV.retAddr t = some ra := by
  unfold SysV.retAddr
  rw [writeRam_eq h]
  simp only [Width.bytes, Mem.loadInt_storeInt_64, Option.map_some, BitVec.ofInt_ofBytes_toBytes_64,
    BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]

end Lift.Spike.Sites.Stack
