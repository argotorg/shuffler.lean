module

public import Lift.Spike.Sites
public import Lift.Spike.L1

@[expose] public section

/-! `toySum`: the sites and the four block lemmas.

```
toySum:  xorl %eax,%eax ; xorl %ecx,%ecx                       (entry)
.LBB1_1: cmpq %rcx,%rsi ; je .LBB1_3                           (head)
         addq (%rdi,%rcx,8),%rax ; incq %rcx ; jmp .LBB1_1     (body)
.LBB1_3: retq                                                  (exit)
``` -/

namespace Lift.Spike.Sites.Sum

open Lift.P2.Total Lift.Sem

/-- `.LBB1_1`, the loop head. -/
def headPC : Int64 := toySumPC + 4
/-- The loop body, after `je`. -/
def bodyPC : Int64 := toySumPC + 9
/-- `.LBB1_3`, the return. -/
def exitPC : Int64 := toySumPC + 18

/-! ## The sites -/

/-- `xorl %eax, %eax`: `af` is undefined. -/
theorem xorAx_step (d : MachineData) :
    L1.step ⟨d, toySumPC⟩ = .require_exec_access ⟨toySumPC, toySumPC + 2⟩ fun _ =>
      .undefined fun af =>
        .done ⟨{ d with regs := { d.regs with rax := 0 }, status := Sites.zeroFlags af },
          toySumPC + 2⟩ := by
  show L1.site17 d = _
  simp [L1.site17, toySumPC, Sites.zeroFlags]

/-- `xorl %ecx, %ecx`: `af` is undefined. -/
theorem xorCx_step (d : MachineData) :
    L1.step ⟨d, toySumPC + 2⟩ = .require_exec_access ⟨toySumPC + 2, headPC⟩ fun _ =>
      .undefined fun af =>
        .done ⟨{ d with regs := { d.regs with rcx := 0 }, status := Sites.zeroFlags af }, headPC⟩ := by
  show L1.site21 d = _
  simp [L1.site21, toySumPC, headPC, Sites.zeroFlags]

/-- `cmpq %rcx, %rsi`. -/
theorem cmp_step (d : MachineData) :
    L1.step ⟨d, headPC⟩ = .require_exec_access ⟨headPC, toySumPC + 7⟩ fun _ =>
      .done ⟨{ d with status := Sites.subFlags d.regs.rsi d.regs.rcx }, toySumPC + 7⟩ := by
  show L1.site22 d = _
  simp [L1.site22, BitVec.take, BitVec.drop, toySumPC, headPC, Sites.subFlags]

/-- `je .LBB1_3`. -/
theorem je_step (d : MachineData) :
    L1.step ⟨d, toySumPC + 7⟩ = .require_exec_access ⟨toySumPC + 7, bodyPC⟩ fun _ =>
      .done ⟨d, if d.status.zf then exitPC else bodyPC⟩ := by
  show L1.site24 d = _
  simp only [L1.site24]
  split <;> rfl

/-- `addq (%rdi,%rcx,8), %rax`. -/
theorem add_step (d : MachineData) :
    L1.step ⟨d, bodyPC⟩ = .require_exec_access ⟨bodyPC, toySumPC + 13⟩ fun _ =>
      d.load (d.regs.rdi.toBitVec + d.regs.rcx.toBitVec * 8) .W64 fun v s =>
        .done ⟨{ s with regs := { s.regs with rax := UInt64.ofBitVec v + s.regs.rax },
                        status := Sites.addFlags (UInt64.ofBitVec v) s.regs.rax }, toySumPC + 13⟩ := by
  show L1.site25 d = _
  simp [L1.site25, BitVec.toAddressSize, BitVec.signed, BitVec.take, BitVec.drop, BitVec.ofInt_add,
    BitVec.ofInt_mul, toySumPC, bodyPC, Sites.addFlags]

/-- `incq %rcx`. -/
theorem inc_step (d : MachineData) :
    L1.step ⟨d, toySumPC + 13⟩ = .require_exec_access ⟨toySumPC + 13, toySumPC + 16⟩ fun _ =>
      .done ⟨{ d with regs := { d.regs with rcx := d.regs.rcx + 1 },
                      status := Sites.incFlags d.regs.rcx d.status.cf }, toySumPC + 16⟩ := by
  show L1.site26 d = _
  simp [L1.site26, BitVec.take, BitVec.drop, toySumPC, Sites.incFlags]

/-- `jmp .LBB1_1`. -/
theorem jmp_step (d : MachineData) :
    L1.step ⟨d, toySumPC + 16⟩ = .require_exec_access ⟨toySumPC + 16, exitPC⟩ fun _ =>
      .done ⟨d, headPC⟩ :=
  rfl

/-- `retq`. -/
theorem ret_step (d : MachineData) :
    L1.step ⟨d, exitPC⟩ = .require_exec_access ⟨exitPC, exitPC + 1⟩ fun _ => Sites.retq d :=
  rfl

/-! ## The site lemmas -/

theorem xorAx_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toySumPC⟩) r ↔
      ∃ af, r = .next ⟨{ d with regs := { d.regs with rax := 0 }, status := Sites.zeroFlags af },
        toySumPC + 2⟩ := by
  rw [xorAx_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.choice_iff]
  simp only [Handled.done_iff]

theorem xorCx_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toySumPC + 2⟩) r ↔
      ∃ af, r = .next ⟨{ d with regs := { d.regs with rcx := 0 }, status := Sites.zeroFlags af },
        headPC⟩ := by
  rw [xorCx_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.choice_iff]
  simp only [Handled.done_iff]

theorem cmp_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, headPC⟩) r ↔
      r = .next ⟨{ d with status := Sites.subFlags d.regs.rsi d.regs.rcx }, toySumPC + 7⟩ := by
  rw [cmp_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.done_iff]

theorem je_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toySumPC + 7⟩) r ↔
      r = .next ⟨d, if d.status.zf then exitPC else bodyPC⟩ := by
  rw [je_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.done_iff]

/-- Each result of `addq` with a readable element `v` adds `v`. -/
theorem add_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (v : UInt64)
    (hread : readRam policy d.dmem (d.regs.rdi.toBitVec + d.regs.rcx.toBitVec * 8) .W64 = .ok v.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, bodyPC⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rax := v + d.regs.rax },
                          status := Sites.addFlags v d.regs.rax }, toySumPC + 13⟩ := by
  rw [add_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Sites.load_iff _ _ _ _ _ _ hread,
    Handled.done_iff, UInt64.ofBitVec_toBitVec]

theorem inc_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toySumPC + 13⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rcx := d.regs.rcx + 1 },
                          status := Sites.incFlags d.regs.rcx d.status.cf }, toySumPC + 16⟩ := by
  rw [inc_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.done_iff]

theorem jmp_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toySumPC + 16⟩) r ↔ r = .next ⟨d, headPC⟩ := by
  rw [jmp_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.done_iff]

theorem ret_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (ra : Int64)
    (hread : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, exitPC⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 } }, ra⟩ := by
  rw [ret_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Sites.retq_iff d ra hread]

/-! ## The blocks

Each block lemma gives `Q` at each exit for each value of the flags: no flag is live at a block
exit. -/

/-- The entry: `rax := 0`, `rcx := 0`, then the loop head. -/
theorem entry {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rax := 0, rcx := 0 }, status := f }, headPC⟩) :
    Reaches L1.step policy Q ⟨d, toySumPC⟩ := by
  refine Sites.Reaches.of_choice _ (xorAx_iff hx d) fun _ => ?_
  refine Sites.Reaches.of_choice _ (xorCx_iff hx _) fun _ => ?_
  exact .done (hQ _)

/-- The loop head: the return block if `rsi = rcx`, else the body. -/
theorem head {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {Q : MachineState → Prop}
    (hexit : d.regs.rsi = d.regs.rcx → ∀ f : StatusFlags, Q ⟨{ d with status := f }, exitPC⟩)
    (hbody : d.regs.rsi ≠ d.regs.rcx → ∀ f : StatusFlags, Q ⟨{ d with status := f }, bodyPC⟩) :
    Reaches L1.step policy Q ⟨d, headPC⟩ := by
  refine Sites.Reaches.of_next _ (cmp_iff hx d) ?_
  refine Sites.Reaches.of_next _ (je_iff hx _) ?_
  rw [Sites.subFlags_zf]
  split
  · rename_i h
    exact .done (hexit (of_decide_eq_true h) _)
  · rename_i h
    exact .done (hbody (fun e => h (decide_eq_true e)) _)

/-- The loop body: `rax := rax + v` for the element `v` at `rdi + 8 * rcx`, `rcx := rcx + 1`, then
the loop head. -/
theorem body {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (v : UInt64)
    (hread : readRam policy d.dmem (d.regs.rdi.toBitVec + d.regs.rcx.toBitVec * 8) .W64 = .ok v.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rax := d.regs.rax + v, rcx := d.regs.rcx + 1 },
                  status := f }, headPC⟩) :
    Reaches L1.step policy Q ⟨d, bodyPC⟩ := by
  refine Sites.Reaches.of_next _ (add_iff hx d v hread) ?_
  refine Sites.Reaches.of_next _ (inc_iff hx _) ?_
  refine Sites.Reaches.of_next _ (jmp_iff hx _) ?_
  rw [UInt64.add_comm d.regs.rax v] at hQ
  exact .done (hQ _)

/-- The return to `ra`. -/
theorem exit {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (ra : Int64)
    (hread : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    {Q : MachineState → Prop}
    (hQ : ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 }, status := f }, ra⟩) :
    Reaches L1.step policy Q ⟨d, exitPC⟩ := by
  refine Sites.Reaches.of_next _ (ret_iff hx d ra hread) ?_
  exact .done (hQ _)

end Lift.Spike.Sites.Sum
