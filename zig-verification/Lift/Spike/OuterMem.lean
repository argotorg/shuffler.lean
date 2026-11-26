module

public import Lift.Sem.Blocks
public import Lift.Sem.Sim
public import Lift.Sem.StackRoom
public import Lift.Spike.Sites
public import Lift.Spike.Sites.Stack
public import Lift.Toys.L1
public import Lift.Tactic.Block
public import Lift.Tactic.FrameMem

@[expose] public section

/-! Answer key and memory experiment; hand chain for L2 only; not an input of the automation.

The caller `toyOuter` of `Lift/Toys/Code.lean` calls `toyTwo` two times. `toyTwo` writes its own
stack room (three pushes and the return word of its calls: 32 bytes below its `rsp`); `toyHalf` has
no stack write. The chain has the caller's blocks and the L2 of the callee as a hypothesis of
`decompiles_l2`. The block lemmas are proved with `lift_block`; the memory goals with `frame_mem`, and
at the two call returns with `frame_call`.
The experiment is in `docs/research/outer-mem-experiment-20261118.md`.

The namespace is `Lift.Toys.OuterMem`, not `Lift.Spike.*`: `Lift/Spike/L1.lean` has its own
`toyEndPC`, `toyTwoPC` and `L1.step`, and inside `Lift.Spike` they hide the ones of the toy unit. -/

namespace Lift.Toys.OuterMem

open Lift.P2.Total Lift.Sem
open Lift.Sem.SysV (Mapped)

def ret1PC : Int64 := 0x100068
def ret2PC : Int64 := 0x100076

theorem entry_block {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyCountPC toyEndPC) (d : MachineData) {m₁ m₂ m₃ m₄ : DataMem}
    (h₁ : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 d.regs.r15.toBitVec = .ok m₁)
    (h₂ : writeRam policy m₁ (d.regs.rsp.toBitVec - 16) .W64 d.regs.r14.toBitVec = .ok m₂)
    (h₃ : writeRam policy m₂ (d.regs.rsp.toBitVec - 24) .W64 d.regs.rbx.toBitVec = .ok m₃)
    (h₄ : writeRam policy m₃ (d.regs.rsp.toBitVec - 32) .W64 ret1PC.toBitVec = .ok m₄)
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with
      regs := { d.regs with rbx := d.regs.rcx, r14 := d.regs.rdx, rsp := d.regs.rsp - 32 },
      dmem := m₄, status := f }, toyTwoPC⟩) :
    Reaches L1.step policy Q ⟨d, toyOuterPC⟩ := by
  lift_block

theorem half1_block {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyCountPC toyEndPC) (d : MachineData) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 ret2PC.toBitVec = .ok m)
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with
      regs := { d.regs with r15 := d.regs.rax, rdi := d.regs.r14, rsi := d.regs.rbx,
                            rsp := d.regs.rsp - 8 },
      dmem := m, status := f }, toyTwoPC⟩) :
    Reaches L1.step policy Q ⟨d, ret1PC⟩ := by
  lift_block

theorem half2_block {policy : CpuPolicy} {Q : MachineState → Prop}
    (hx : SysV.ExecRange policy toyCountPC toyEndPC) (d : MachineData) {b c e : UInt64}
    {ra : Int64}
    (h₁ : readRam policy d.dmem d.regs.rsp.toBitVec .W64 = .ok b.toBitVec)
    (h₂ : readRam policy d.dmem (d.regs.rsp.toBitVec + 8) .W64 = .ok c.toBitVec)
    (h₃ : readRam policy d.dmem (d.regs.rsp.toBitVec + 16) .W64 = .ok e.toBitVec)
    (h₄ : readRam policy d.dmem (d.regs.rsp.toBitVec + 24) .W64 = .ok ra.toBitVec)
    (hQ : ∀ f : StatusFlags, Q ⟨{ d with
      regs := { d.regs with rax := d.regs.r15 + d.regs.rax, rbx := b, r14 := c, r15 := e,
                            rsp := d.regs.rsp + 32 },
      status := f }, ra⟩) :
    Reaches L1.step policy Q ⟨d, ret2PC⟩ := by
  lift_block

/-! ## The models -/

/-- The four arguments. -/
abbrev Args := UInt64 × UInt64 × UInt64 × UInt64

/-- The entry of `toyOuter`: four arguments, a stack room of 64 bytes (24 of pushes, 8 for the return
word of the call, 32 for the room of `toyTwo`). -/
def rep (policy : CpuPolicy) (x : Args) (s : MachineState) : Prop :=
  SysV.Entry policy toyCountPC toyEndPC toyOuterPC s ∧ s.data.regs.rdi = x.1 ∧
    s.data.regs.rsi = x.2.1 ∧ s.data.regs.rdx = x.2.2.1 ∧ s.data.regs.rcx = x.2.2.2 ∧
    SysV.StackRoom policy s 64

/-- The return: the result in `rax`; each byte outside the 64 bytes below `rsp` is unchanged. -/
def post (_ : Args) (y : UInt64) (s t : MachineState) : Prop :=
  SysV.Exit s t ∧ t.data.regs.rax = y ∧ SysV.Outside s 64 t.data.dmem

/-- The callee `toyTwo` of the unit of `Lift/Toys/Code.lean`: two arguments, a room of 32 bytes. -/
def repTwo (policy : CpuPolicy) (ab : UInt64 × UInt64) (s : MachineState) : Prop :=
  SysV.Entry policy toyCountPC toyEndPC toyTwoPC s ∧ s.data.regs.rdi = ab.1 ∧
    s.data.regs.rsi = ab.2 ∧ SysV.StackRoom policy s 32

/-- The return of `toyTwo`: the bytes outside its room are unchanged and the words of the room are
still mapped. -/
def postTwo (_ : UInt64 × UInt64) (y : UInt64) (s t : MachineState) : Prop :=
  SysV.Exit s t ∧ t.data.regs.rax = y ∧ SysV.Outside s 32 t.data.dmem ∧
    Mapped s.data.regs.rsp.toBitVec 8 32 t.data.dmem

def two : Model (UInt64 × UInt64) UInt64 where
  rep := repTwo
  returns ab y := y = (ab.1 >>> 1) + (ab.2 >>> 1)
  post := postTwo

inductive Lbl where
  | entry
  | half1
  | half2

/-- L2: `toyTwo(a, b)`, `toyTwo(c, d)`, the sum. The second and third components of the state at
`half1` and `half2` are `c`, `d`, and `0` where unused. -/
def blocks : Blocks Lbl Args UInt64 Unit (fun _ => UInt64 × UInt64) (fun _ => UInt64) where
  step
    | .entry, (a, b, c, d) => .ok (.call () (a, b) fun x => (.half1, (x, c, d, 0)))
    | .half1, (x, c, d, _) => .ok (.call () (c, d) fun y => (.half2, (x, y, 0, 0)))
    | .half2, (x, y, _, _) => .ok (.ret (x + y))

def l2 : Model Args UInt64 where
  rep := rep
  returns x y := blocks.Returns (fun _ => two.returns) .entry x y
  post := post

/-! ## The frame -/

/-- The frame in `m`: the `r15`, `r14` and `rbx` of `s₀` at `rsp - 8`, `rsp - 16`, `rsp - 24`, the
bytes outside the room unchanged, and the words below the saved registers mapped. -/
def Frame (policy : CpuPolicy) (s₀ : MachineState) (m : DataMem) : Prop :=
  readRam policy m (s₀.data.regs.rsp.toBitVec - 8) .W64 = .ok s₀.data.regs.r15.toBitVec ∧
    readRam policy m (s₀.data.regs.rsp.toBitVec - 16) .W64 = .ok s₀.data.regs.r14.toBitVec ∧
    readRam policy m (s₀.data.regs.rsp.toBitVec - 24) .W64 = .ok s₀.data.regs.rbx.toBitVec ∧
    SysV.Outside s₀ 64 m ∧ Mapped s₀.data.regs.rsp.toBitVec 32 64 m

def Kept (s u : MachineState) : Prop :=
  u.data.regs.rbp = s.data.regs.rbp ∧ u.data.regs.r12 = s.data.regs.r12 ∧
    u.data.regs.r13 = s.data.regs.r13

def at_ (policy : CpuPolicy) (x : Args) (s₀ : MachineState) :
    Lbl → Args → MachineState → Prop
  | .entry, y, s => s = s₀ ∧ rep policy x s ∧ y = x
  | .half1, (z, c, d, _), u => rep policy x s₀ ∧ u.pc = ret1PC ∧ u.data.regs.rax = z ∧
      u.data.regs.rbx = d ∧ u.data.regs.r14 = c ∧ u.data.regs.r15 = s₀.data.regs.r15 ∧
      u.data.regs.rsp = s₀.data.regs.rsp - 24 ∧ Kept s₀ u ∧ Frame policy s₀ u.data.dmem
  | .half2, (z, y, _, _), u => rep policy x s₀ ∧ u.pc = ret2PC ∧ u.data.regs.r15 = z ∧
      u.data.regs.rax = y ∧ u.data.regs.rsp = s₀.data.regs.rsp - 24 ∧ Kept s₀ u ∧
      Frame policy s₀ u.data.dmem

/-! ## The blocks -/

theorem entry_retAddr {policy : CpuPolicy} (d : MachineData) {m₃ m₄ : DataMem}
    (h₄ : writeRam policy m₃ (d.regs.rsp.toBitVec - 32) .W64 ret1PC.toBitVec = .ok m₄)
    (f : StatusFlags) :
    SysV.retAddr ⟨{ d with
      regs := { d.regs with rbx := d.regs.rcx, r14 := d.regs.rdx, rsp := d.regs.rsp - 32 },
      dmem := m₄, status := f }, toyTwoPC⟩ = some ret1PC :=
  Lift.Spike.Sites.Stack.retAddr_writeRam (by simpa [UInt64.toBitVec_sub] using h₄)

theorem entry_code {policy : CpuPolicy} {x : Args} {s₀ : MachineState} (h : rep policy x s₀) :
    Reaches L1.step policy (fun t => repTwo policy (x.1, x.2.1) t ∧
      ∀ z u, postTwo (x.1, x.2.1) z t u →
        at_ policy x s₀ .half1 (z, x.2.2.1, x.2.2.2, 0) u) s₀ := by
  obtain ⟨he, ha, hb, hc, hd, room⟩ := h
  obtain ⟨d, pc⟩ := s₀
  obtain rfl : pc = toyOuterPC := he.pc
  refine' entry_block he.exec d ?h₁ ?h₂ ?h₃ ?h₄ fun f =>
    have hret := entry_retAddr d ?h₄ f
    ⟨⟨⟨rfl, he.exec, ?perm, ret1PC, hret⟩, ha, hb, ?room32⟩, ?post⟩
  any_goals frame_call
  case post =>
    rintro z u ⟨⟨hpc, hsp, hbx, hbp, h12, h13, h14, h15⟩, hz, out, mp⟩
    rw [hret, Option.some.injEq] at hpc
    have e : d.regs.rsp - 32 + 8 = d.regs.rsp - 24 := by bv_decide
    simp only [at_, Frame]
    refine ⟨⟨he, ha, hb, hc, hd, room⟩, hpc.symm, hz, hbx.trans hd, h14.trans hc, h15, hsp.trans e,
      ⟨hbp, h12, h13⟩, ?r15s, ?r14s, ?rbxs, ?out, ?map⟩
    any_goals frame_call

theorem half1_retAddr {policy : CpuPolicy} (d : MachineData) {m : DataMem}
    (h : writeRam policy d.dmem (d.regs.rsp.toBitVec - 8) .W64 ret2PC.toBitVec = .ok m)
    (f : StatusFlags) :
    SysV.retAddr ⟨{ d with
      regs := { d.regs with r15 := d.regs.rax, rdi := d.regs.r14, rsi := d.regs.rbx,
                            rsp := d.regs.rsp - 8 },
      dmem := m, status := f }, toyTwoPC⟩ = some ret2PC :=
  Lift.Spike.Sites.Stack.retAddr_writeRam (by simpa [UInt64.toBitVec_sub] using h)

theorem half1_code {policy : CpuPolicy} {x : Args} {s₀ u : MachineState} {z c e g : UInt64}
    (h : at_ policy x s₀ .half1 (z, c, e, g) u) :
    Reaches L1.step policy (fun t => repTwo policy (c, e) t ∧
      ∀ w v, postTwo (c, e) w t v → at_ policy x s₀ .half2 (z, w, 0, 0) v) u := by
  obtain ⟨d, pc⟩ := u
  dsimp only [at_] at h
  obtain ⟨hrep, rfl, hax, hbx, h14, h15, hsp, ⟨hbp, h12, h13⟩, r15s, r14s, rbxs, out, mp⟩ := h
  have room := hrep.2.2.2.2.2
  refine' half1_block hrep.1.exec d ?hw fun f =>
    have hret := half1_retAddr d ?hw f
    ⟨⟨⟨rfl, hrep.1.exec, ?perm, ret2PC, hret⟩, h14, hbx, ?room32⟩, ?post⟩
  any_goals frame_call
  case post =>
    rintro w v ⟨⟨hpc, hsp', hbx', hbp', h12', h13', h14', h15'⟩, hw, out', mp'⟩
    rw [hret, Option.some.injEq] at hpc
    simp only [at_, Frame]
    refine ⟨hrep, hpc.symm, h15'.trans hax, hw, hsp'.trans (by rw [hsp]; bv_decide),
      ⟨hbp'.trans hbp, h12'.trans h12, h13'.trans h13⟩, ?r15s, ?r14s, ?rbxs, ?out, ?map⟩
    any_goals frame_call

theorem half2_code {policy : CpuPolicy} {x : Args} {s₀ u : MachineState} {z y g₁ g₂ : UInt64}
    (h : at_ policy x s₀ .half2 (z, y, g₁, g₂) u) :
    Reaches L1.step policy (post x (z + y) s₀) u := by
  obtain ⟨d, pc⟩ := u
  dsimp only [at_] at h
  obtain ⟨⟨he, -, -, -, -, room⟩, rfl, h15, hax, hsp, ⟨hbp, h12, h13⟩, r15s, r14s, rbxs, out, mp⟩ := h
  obtain ⟨ra, hra⟩ := he.ret
  have hret := Lift.Spike.Sites.readRet he hra
  have e32 : d.regs.rsp + 32 = s₀.data.regs.rsp + 8 := by rw [hsp]; bv_decide
  refine' half2_block he.exec d ?h₁ ?h₂ ?h₃ ?h₄ fun f =>
    ⟨⟨hra, e32, rfl, hbp, h12, h13, rfl, rfl⟩, ?_, out⟩
  any_goals frame_mem
  show d.regs.r15 + d.regs.rax = z + y
  rw [h15, hax]

/-! ## The chain -/

/-- The chain of the caller, from the L2 of the callee as a hypothesis. -/
theorem decompiles_l2 (hc : Decompiles L1.step two) : Decompiles L1.step l2 := by
  refine Decompiles.ofBlocks blocks (fun _ => two) (fun _ => hc) .entry id at_
    (fun _ _ h => h) (fun _ _ _ h => ⟨rfl, h, rfl⟩) ?_
  rintro policy x s₀ (_ | _ | _) ⟨z, c, e, g⟩ s hat n hn <;>
    simp only [blocks, Res.ok.injEq] at hn <;> subst hn
  · obtain ⟨rfl, h, rfl⟩ := hat
    exact entry_code h
  · exact half1_code hat
  · exact half2_code hat

end Lift.Toys.OuterMem
