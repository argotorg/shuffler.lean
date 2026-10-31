import BbuKraken.Unit.Plan.PlannerRunPrepare

namespace Bbu.Unit.PlannerRunU
open Flat

structure InitLI (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends LoopLI P g F s ra lo locals t where
  r13 : t.regs.r13.toBitVec = t.regs.rsp.toBitVec + 32#64
  count : locals[3]? = some g.countPtr
  targets : Flat.targetsFrom g.p.fl g.spills 0 = true
  rdx : t.regs.rdx.toBitVec = g.p.m
  rsi : t.regs.rsi.toBitVec = g.p.n

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo locals : List Word}

theorem InitLI.next (h : InitLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13)
    (hdx : u.regs.rdx = t.regs.rdx) (hsi : u.regs.rsi = t.regs.rsi) :
    InitLI P g F s ra lo locals u := by
  refine ⟨h.toLoopLI.next hm hsp hbx h12 h15 hbp h14, ?_, h.count,
    h.targets, hdx ▸ h.rdx, hsi ▸ h.rsi⟩
  simpa only [h13, hsp] using h.r13

theorem InitLI.storeLocal (h : InitLI P g F s ra lo locals t) {i : Nat}
    (hi : i < 4121) (hlo : 4 ≤ i) (w : Word)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13)
    (hdx : u.regs.rdx = t.regs.rdx) (hsi : u.regs.rsi = t.regs.rsi) :
    InitLI P g F s ra lo (locals.set i w) u := by
  refine ⟨⟨h.toBd.storeLocal hi w hm hsp, hbx ▸ h.rbx, h12 ▸ h.r12,
    h15 ▸ h.r15, h14 ▸ h.r14, ?_⟩, ?_, ?_, h.targets,
    hdx ▸ h.rdx, hsi ▸ h.rsi⟩
  · simpa only [List.getElem?_set, show i ≠ 2 by omega,
      show 2 ≠ i by omega, ↓reduceIte] using h.sources
  · simpa only [h13, hsp] using h.r13
  · simpa only [List.getElem?_set, show i ≠ 3 by omega,
      show 3 ≠ i by omega, ↓reduceIte] using h.count

end

def InitPrefix (locals : List Word) (base count : Nat) : Prop :=
  ∀ i, i < count → locals[base + i]? = some NONE

def InitDestHead (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, InitLI P g F s ra lo locals t ∧ rax t < g.p.m ∧
    InitPrefix locals 12 (rax t).toNat

def InitDestDone (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, InitLI P g F s ra lo locals t ∧ InitPrefix locals 12 g.p.m.toNat

def InitPosHead (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals i, InitLI P g F s ra lo locals t ∧ i < g.p.n ∧
    rax t = t.regs.rsp.toBitVec + 96#64 + i * 8#64 ∧
    rcx t = t.regs.rsp.toBitVec + 96#64 + g.p.n * 8#64 ∧
    InitPrefix locals 12 g.p.m.toNat ∧ InitPrefix locals 1036 i.toNat

def InitDone (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, InitLI P g F s ra lo locals t ∧
    InitPrefix locals 12 g.p.m.toNat ∧ InitPrefix locals 1036 g.p.n.toNat

theorem InitPrefix.zero (locals : List Word) (base : Nat) : InitPrefix locals base 0 := by
  intro i hi
  exact False.elim (Nat.not_lt_zero i hi)

theorem InitPrefix.step {locals : List Word} {base count : Nat}
    (h : InitPrefix locals base count) (hi : base + count < locals.length) :
    InitPrefix (locals.set (base + count) NONE) base (count + 1) := by
  intro i hi'
  by_cases he : i = count
  · subst i
    exact List.getElem?_set_self hi
  · simpa only [List.getElem?_set, show base + i ≠ base + count by omega,
      show base + count ≠ base + i by omega, ↓reduceIte] using h i (by omega)

theorem InitPrefix.set_outside {locals : List Word} {base count index : Nat}
    (h : InitPrefix locals base count) (hout : ∀ i, i < count → base + i ≠ index)
    (w : Word) : InitPrefix (locals.set index w) base count := by
  intro i hi
  simpa only [List.getElem?_set, hout i hi, Ne.symm (hout i hi), ↓reduceIte]
    using h i hi

end Bbu.Unit.PlannerRunU
