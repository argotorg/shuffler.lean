module

public import Lift.Spike.Sites
public import Lift.Spike.L1

@[expose] public section

/-! `toyMark` (`movb $1, (%rdi,%rsi) ; retq`): the sites and the block lemma. -/

namespace Lift.Spike.Sites.Mark

open Lift.P2.Total Lift.Sem

/-- `movb $1, (%rdi,%rsi)`. -/
theorem mov_step (d : MachineData) :
    L1.step ⟨d, toyMarkPC⟩ = .require_exec_access ⟨toyMarkPC, toyMarkPC + 4⟩ fun _ =>
      d.store (d.regs.rdi.toBitVec + d.regs.rsi.toBitVec) (w := .W8) 1 fun s =>
        .done ⟨s, toyMarkPC + 4⟩ := by
  show L1.site52 d = _
  simp [L1.site52, BitVec.toAddressSize, BitVec.signed, BitVec.take, BitVec.ofInt_add, toyMarkPC]

/-- `retq`. -/
theorem ret_step (d : MachineData) :
    L1.step ⟨d, toyMarkPC + 4⟩ = .require_exec_access ⟨toyMarkPC + 4, toyMarkPC + 5⟩ fun _ =>
      Sites.retq d :=
  rfl

/-- Each result of `movb` is the next state with the memory `m` that `writeRam` gives. -/
theorem mov_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {m : DataMem}
    (hwrite : writeRam policy d.dmem (d.regs.rdi.toBitVec + d.regs.rsi.toBitVec) .W8 1 = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toyMarkPC⟩) r ↔
      r = .next ⟨{ d with dmem := m }, toyMarkPC + 4⟩ := by
  rw [mov_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Sites.store_iff _ _ _ _ _ _ _ hwrite,
    Handled.done_iff]

theorem ret_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (ra : Int64)
    (hread : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toyMarkPC + 4⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 } }, ra⟩ := by
  rw [ret_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Sites.retq_iff d ra hread]

/-! ## The block -/

/-- The one block: the byte `1` at `rdi + rsi`, then the return to `ra`. The return word is read
from the memory after the store. -/
theorem block {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (m : DataMem) (ra : Int64)
    (hwrite : writeRam policy d.dmem (d.regs.rdi.toBitVec + d.regs.rsi.toBitVec) .W8 1 = .ok m)
    (hread : readRam policy m d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 }, status := f, dmem := m }, ra⟩) :
    Reaches L1.step policy Q ⟨d, toyMarkPC⟩ := by
  refine Sites.Reaches.of_next _ (mov_iff hx d hwrite) ?_
  refine Sites.Reaches.of_next _ (ret_iff hx _ ra hread) ?_
  exact .done (hQ _)

end Lift.Spike.Sites.Mark
