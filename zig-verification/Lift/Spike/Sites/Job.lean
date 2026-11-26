module

public import Lift.Spike.Sites.Stack

@[expose] public section

/-! T5 `toyJob`: the site equation and the site lemma of each instruction, and one block lemma
for each basic block.

```
toyJob (0x100000): movq 8(%rdi),%rsi ; cmpq 16(%rdi),%rsi ; jbe .LBB0_3
       (0x10000a): pushq $1 ; popq %rax ; retq
.LBB0_3 (0x10000e): pushq %rbx ; movq %rdi,%rbx ; movq (%rdi),%rdi ; callq toySum
       (0x10001a): movq %rax,24(%rbx) ; xorl %eax,%eax ; popq %rbx ; retq
```

A block lemma has one hypothesis for each memory access, in the order of the code; a later access
is on the memory after the earlier writes. The flags at the exit are any flags (see
`Lift/Spike/Sites/Stack.lean`). -/

namespace Lift.Spike.Sites.Job

open Lift.P2.Total Lift.Sem

/-- The block of `len > limit`. -/
def tooLongPC : Int64 := 0x10000a

/-- The block of `len ≤ limit` (`.LBB0_3`), which calls `toySum`. -/
def callSumPC : Int64 := 0x10000e

/-- The return point of the call of `toySum`. -/
def retSumPC : Int64 := 0x10001a

/-! ## Site equations -/

/-- `movq 8(%rdi), %rsi`. -/
theorem movRsi_step (d : MachineData) :
    L1.step ⟨d, toyJobPC⟩ = .require_exec_access ⟨toyJobPC, 0x100004⟩ fun _ =>
      d.load (d.regs.rdi.toBitVec + 8) .W64 fun v s =>
        .done ⟨{ s with regs := { s.regs with rsi := UInt64.ofBitVec v } }, 0x100004⟩ := by
  show L1.site2 d = _
  simp [L1.site2, BitVec.toAddressSize, BitVec.signed, BitVec.take, BitVec.ofInt_add, toyJobPC]

/-- `cmpq 16(%rdi), %rsi`. -/
theorem cmp_step (d : MachineData) :
    L1.step ⟨d, 0x100004⟩ = .require_exec_access ⟨0x100004, 0x100008⟩ fun _ =>
      d.load (d.regs.rdi.toBitVec + 16) .W64 fun b s =>
        .done ⟨{ s with status := Sites.subFlags d.regs.rsi (UInt64.ofBitVec b) }, 0x100008⟩ := by
  show L1.site3 d = _
  simp [L1.site3, Sites.subFlags, BitVec.toAddressSize, BitVec.signed, BitVec.drop, BitVec.take,
    BitVec.ofInt_add]

/-- `jbe .LBB0_3`. -/
theorem jbe_step (d : MachineData) :
    L1.step ⟨d, 0x100008⟩ = .require_exec_access ⟨0x100008, tooLongPC⟩ fun _ =>
      if d.status.cf = true ∨ d.status.zf = true then .done ⟨d, callSumPC⟩
      else .done ⟨d, tooLongPC⟩ :=
  rfl

/-- `pushq $1`. -/
theorem push1_step (d : MachineData) :
    L1.step ⟨d, tooLongPC⟩ = .require_exec_access ⟨tooLongPC, 0x10000c⟩ fun _ =>
      Stack.push d 1 0x10000c :=
  rfl

/-- `popq %rax`. -/
theorem popRax_step (d : MachineData) :
    L1.step ⟨d, 0x10000c⟩ = .require_exec_access ⟨0x10000c, 0x10000d⟩ fun _ =>
      d.load d.regs.rsp.toBitVec .W64 fun v s =>
        .done ⟨{ s with regs := { s.regs with rax := UInt64.ofBitVec v, rsp := d.regs.rsp + 8 } },
          0x10000d⟩ :=
  rfl

/-- `retq` (of `len > limit`). -/
theorem ret1_step (d : MachineData) :
    L1.step ⟨d, 0x10000d⟩ = .require_exec_access ⟨0x10000d, callSumPC⟩ fun _ => Sites.retq d :=
  rfl

/-- `pushq %rbx`. -/
theorem pushRbx_step (d : MachineData) :
    L1.step ⟨d, callSumPC⟩ = .require_exec_access ⟨callSumPC, 0x10000f⟩ fun _ =>
      Stack.push d d.regs.rbx.toBitVec 0x10000f := by
  show L1.site9 d = _
  simp [L1.site9, Stack.push, BitVec.drop, BitVec.take, callSumPC]

/-- `movq %rdi, %rbx`. -/
theorem movRbx_step (d : MachineData) :
    L1.step ⟨d, 0x10000f⟩ = .require_exec_access ⟨0x10000f, 0x100012⟩ fun _ =>
      .done ⟨{ d with regs := { d.regs with rbx := d.regs.rdi } }, 0x100012⟩ := by
  show L1.site10 d = _
  simp [L1.site10, BitVec.drop, BitVec.take]

/-- `movq (%rdi), %rdi`. -/
theorem movRdi_step (d : MachineData) :
    L1.step ⟨d, 0x100012⟩ = .require_exec_access ⟨0x100012, 0x100015⟩ fun _ =>
      d.load d.regs.rdi.toBitVec .W64 fun v s =>
        .done ⟨{ s with regs := { s.regs with rdi := UInt64.ofBitVec v } }, 0x100015⟩ := by
  show L1.site11 d = _
  simp [L1.site11, BitVec.toAddressSize, BitVec.signed, BitVec.take]

/-- `callq toySum`. -/
theorem call_step (d : MachineData) :
    L1.step ⟨d, 0x100015⟩ = .require_exec_access ⟨0x100015, retSumPC⟩ fun _ =>
      Stack.call d retSumPC toySumPC :=
  rfl

/-- `movq %rax, 24(%rbx)`. -/
theorem store_step (d : MachineData) :
    L1.step ⟨d, retSumPC⟩ = .require_exec_access ⟨retSumPC, 0x10001e⟩ fun _ =>
      d.store (d.regs.rbx.toBitVec + 24) d.regs.rax.toBitVec fun s => .done ⟨s, 0x10001e⟩ := by
  show L1.site13 d = _
  simp [L1.site13, BitVec.toAddressSize, BitVec.signed, BitVec.drop, BitVec.take, BitVec.ofInt_add,
    retSumPC]

/-- `xorl %eax, %eax`: `af` is undefined. -/
theorem xor_step (d : MachineData) :
    L1.step ⟨d, 0x10001e⟩ = .require_exec_access ⟨0x10001e, 0x100020⟩ fun _ =>
      .undefined fun af : Bool => .done ⟨{ d with
        regs := { d.regs with rax := 0 },
        status := StatusFlags.from_result (0#32) ⟨false, af, false⟩ }, 0x100020⟩ :=
  rfl

/-- `popq %rbx`. -/
theorem popRbx_step (d : MachineData) :
    L1.step ⟨d, 0x100020⟩ = .require_exec_access ⟨0x100020, 0x100021⟩ fun _ =>
      d.load d.regs.rsp.toBitVec .W64 fun v s =>
        .done ⟨{ s with regs := { s.regs with rbx := UInt64.ofBitVec v, rsp := d.regs.rsp + 8 } },
          0x100021⟩ :=
  rfl

/-- `retq` (of `len ≤ limit`). -/
theorem ret2_step (d : MachineData) :
    L1.step ⟨d, 0x100021⟩ = .require_exec_access ⟨0x100021, 0x100022⟩ fun _ => Sites.retq d :=
  rfl

/-! ## Site lemmas -/

theorem movRsi_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {len : UInt64}
    (h : readRam policy d.dmem (d.regs.rdi.toBitVec + 8) .W64 = .ok len.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, toyJobPC⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsi := len } }, 0x100004⟩ := by
  rw [movRsi_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.load_done_iff _ _ _ _ h]

theorem cmp_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {limit : UInt64}
    (h : readRam policy d.dmem (d.regs.rdi.toBitVec + 16) .W64 = .ok limit.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x100004⟩) r ↔
      r = .next ⟨{ d with status := Sites.subFlags d.regs.rsi limit }, 0x100008⟩ := by
  rw [cmp_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.load_done_iff _ _ _ _ h]

theorem jbe_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x100008⟩) r ↔
      r = .next ⟨d, if d.status.cf = true ∨ d.status.zf = true then callSumPC else tooLongPC⟩ := by
  rw [jbe_step, Sites.exec_iff hx _ _ _ _ _ (by decide)]
  split <;> exact Handled.done_iff _ _ _ _ _

theorem push1_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 1 = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, tooLongPC⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp - 8 }, dmem := m }, 0x10000c⟩ := by
  rw [push1_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.push_iff _ _ _ h]

theorem popRax_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {v : UInt64}
    (h : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok v.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x10000c⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rax := v, rsp := d.regs.rsp + 8 } }, 0x10000d⟩ := by
  rw [popRax_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.load_done_iff _ _ _ _ h]

theorem ret1_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {ra : Int64}
    (h : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x10000d⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 } }, ra⟩ := by
  rw [ret1_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Sites.retq_iff d ra h]

theorem pushRbx_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 d.regs.rbx.toBitVec = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, callSumPC⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp - 8 }, dmem := m }, 0x10000f⟩ := by
  rw [pushRbx_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.push_iff _ _ _ h]

theorem movRbx_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x10000f⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rbx := d.regs.rdi } }, 0x100012⟩ := by
  rw [movRbx_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.done_iff]

theorem movRdi_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {v : UInt64}
    (h : readRam policy d.dmem d.regs.rdi.toBitVec .W64 = .ok v.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x100012⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rdi := v } }, 0x100015⟩ := by
  rw [movRdi_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.load_done_iff _ _ _ _ h]

theorem call_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 retSumPC.toBitVec = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x100015⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp - 8 }, dmem := m }, toySumPC⟩ := by
  rw [call_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.call_iff _ _ _ h]

theorem store_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rbx.toBitVec + 24) .W64 d.regs.rax.toBitVec = .ok m)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, retSumPC⟩) r ↔
      r = .next ⟨{ d with dmem := m }, 0x10001e⟩ := by
  rw [store_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.store_done_iff _ _ _ _ h]

theorem xor_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x10001e⟩) r ↔
      ∃ af : Bool, r = .next ⟨{ d with
        regs := { d.regs with rax := 0 },
        status := StatusFlags.from_result (0#32) ⟨false, af, false⟩ }, 0x100020⟩ := by
  rw [xor_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Handled.choice_iff]
  simp only [Handled.done_iff]

theorem popRbx_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {v : UInt64}
    (h : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok v.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x100020⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rbx := v, rsp := d.regs.rsp + 8 } }, 0x100021⟩ := by
  rw [popRbx_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Stack.load_done_iff _ _ _ _ h]

theorem ret2_iff {policy : CpuPolicy} (hx : SysV.ExecRange policy toyJobPC toyEndPC)
    (d : MachineData) {ra : Int64}
    (h : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    (r : StepResult DataMem) :
    Handled policy id d.dmem (L1.step ⟨d, 0x100021⟩) r ↔
      r = .next ⟨{ d with regs := { d.regs with rsp := d.regs.rsp + 8 } }, ra⟩ := by
  rw [ret2_step, Sites.exec_iff hx _ _ _ _ _ (by decide), Sites.retq_iff d ra h]

/-! ## Block lemmas -/

/-- The entry block: `len` at `rdi + 8` goes to `rsi`, the compare with `limit` at `rdi + 16`, and
the branch on the unsigned `len ≤ limit`. -/
theorem entry {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData) {len limit : UInt64}
    (hlen : readRam policy d.dmem (d.regs.rdi.toBitVec + 8) .W64 = .ok len.toBitVec)
    (hlimit : readRam policy d.dmem (d.regs.rdi.toBitVec + 16) .W64 = .ok limit.toBitVec)
    (hle : len ≤ limit → ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rsi := len }, status := f }, callSumPC⟩)
    (hgt : limit < len → ∀ f : StatusFlags,
      Q ⟨{ d with regs := { d.regs with rsi := len }, status := f }, tooLongPC⟩) :
    Reaches L1.step policy Q ⟨d, toyJobPC⟩ := by
  refine Sites.Reaches.of_next _ (movRsi_iff hx d hlen) ?_
  refine Sites.Reaches.of_next _ (cmp_iff hx _ hlimit) ?_
  refine Sites.Reaches.of_next _ (jbe_iff hx _) ?_
  split
  next hc => exact .done (hle ((Sites.subFlags_be len limit).mp hc) _)
  next hc => exact .done (hgt (UInt64.not_le.mp (mt (Sites.subFlags_be len limit).mpr hc)) _)

/-- The block of `len > limit`: `rax := 1` through the stack, and the return. -/
theorem tooLong {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData) {m : DataMem} {ra : Int64}
    (h₁ : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 1 = .ok m)
    (h₂ : readRam policy m (d.regs.rsp.toBitVec - 8) .W64 = .ok 1)
    (h₃ : readRam policy m d.regs.rsp.toBitVec .W64 = .ok ra.toBitVec)
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with
      regs := { d.regs with rax := 1, rsp := d.regs.rsp + 8 },
      dmem := m, status := f }, ra⟩) :
    Reaches L1.step policy Q ⟨d, tooLongPC⟩ := by
  refine Sites.Reaches.of_next _ (push1_iff hx d h₁) ?_
  refine Sites.Reaches.of_next _
    (popRax_iff hx _ (v := 1) (by simpa [UInt64.toBitVec_sub] using h₂)) ?_
  refine Sites.Reaches.of_next _ (ret1_iff hx _ (by simpa using h₃)) ?_
  have e : d.regs.rsp + 8 = d.regs.rsp - 8 + 8 + 8 := by bv_decide
  simp only [e] at hQ
  exact .done (hQ _)

/-- The block of `len ≤ limit`: push `rbx`, `rbx := rdi`, `rdi := src` from `(rdi)`, and the call
of `toySum` with the return address `retSumPC` at `rsp - 16`. -/
theorem callSum {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData) {m₁ m₂ : DataMem}
    {src : UInt64}
    (h₁ : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 d.regs.rbx.toBitVec = .ok m₁)
    (h₂ : readRam policy m₁ d.regs.rdi.toBitVec .W64 = .ok src.toBitVec)
    (h₃ : writeRam policy m₁ (d.regs.rsp.toBitVec - 16) .W64 retSumPC.toBitVec = .ok m₂)
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with
      regs := { d.regs with rbx := d.regs.rdi, rdi := src, rsp := d.regs.rsp - 16 },
      dmem := m₂, status := f }, toySumPC⟩) :
    Reaches L1.step policy Q ⟨d, callSumPC⟩ := by
  refine Sites.Reaches.of_next _ (pushRbx_iff hx d h₁) ?_
  refine Sites.Reaches.of_next _ (movRbx_iff hx _) ?_
  refine Sites.Reaches.of_next _ (movRdi_iff hx _ h₂) ?_
  refine Sites.Reaches.of_next _
    (call_iff hx _ (by simpa [UInt64.toBitVec_sub, BitVec.sub_sub] using h₃)) ?_
  have e : d.regs.rsp - 16 = d.regs.rsp - 8 - 8 := by bv_decide
  simp only [e] at hQ
  exact .done (hQ _)

/-- At the exit of `callSum`, the return address is `retSumPC`. -/
theorem callSum_retAddr {policy : CpuPolicy} (d : MachineData) {m₁ m₂ : DataMem} {src : UInt64}
    (h₃ : writeRam policy m₁ (d.regs.rsp.toBitVec - 16) .W64 retSumPC.toBitVec = .ok m₂)
    (f : StatusFlags) :
    SysV.retAddr ⟨{ d with
      regs := { d.regs with rbx := d.regs.rdi, rdi := src, rsp := d.regs.rsp - 16 },
      dmem := m₂, status := f }, toySumPC⟩ = some retSumPC :=
  Stack.retAddr_writeRam (by simpa [UInt64.toBitVec_sub] using h₃)

/-- The block after the call of `toySum`: the store of `rax` at `rbx + 24`, `rax := 0`, `rbx`
back from `rsp`, and the return to the word at `rsp + 8`. -/
theorem sumRet {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyJobPC toyEndPC) (d : MachineData) {m : DataMem}
    {b : UInt64} {ra : Int64}
    (h₁ : writeRam policy d.dmem (d.regs.rbx.toBitVec + 24) .W64 d.regs.rax.toBitVec = .ok m)
    (h₂ : readRam policy m d.regs.rsp.toBitVec .W64 = .ok b.toBitVec)
    (h₃ : readRam policy m (d.regs.rsp.toBitVec + 8) .W64 = .ok ra.toBitVec)
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with
      regs := { d.regs with rax := 0, rbx := b, rsp := d.regs.rsp + 16 },
      dmem := m, status := f }, ra⟩) :
    Reaches L1.step policy Q ⟨d, retSumPC⟩ := by
  refine Sites.Reaches.of_next _ (store_iff hx d h₁) ?_
  refine Sites.Reaches.of_choice _ (xor_iff hx _) fun _ => ?_
  refine Sites.Reaches.of_next _ (popRbx_iff hx _ h₂) ?_
  refine Sites.Reaches.of_next _
    (ret2_iff hx _ (by simpa [UInt64.toBitVec_add] using h₃)) ?_
  have e : d.regs.rsp + 16 = d.regs.rsp + 8 + 8 := by bv_decide
  simp only [e] at hQ
  exact .done (hQ _)

end Lift.Spike.Sites.Job
