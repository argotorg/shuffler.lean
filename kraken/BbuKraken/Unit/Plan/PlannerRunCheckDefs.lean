import BbuKraken.Unit.Plan.PlannerRunFrame
import BbuKraken.Unit.Plan.PlannerRunModel

namespace Bbu.Unit.PlannerRunU

structure LoopLI (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends Bd P g F s ra lo locals t where
  rbx : t.regs.rbx.toBitVec = P
  r12 : t.regs.r12.toBitVec = g.dataPtr
  r15 : t.regs.r15.toBitVec = g.opsPtr
  r14 : t.regs.r14.toBitVec.setWidth 8 = (rsi s).setWidth 8
  sources : locals[2]? = some g.sourcesPtr

structure EarlyLI (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends Bd P g F s ra lo locals t where
  rbx : t.regs.rbx.toBitVec = P
  r12 : t.regs.r12.toBitVec = g.dataPtr
  r15 : t.regs.r15.toBitVec = g.opsPtr
  rbp : t.regs.rbp.toBitVec = g.countPtr
  r14 : t.regs.r14.toBitVec.setWidth 8 = (rsi s).setWidth 8
  sources : locals[2]? = some g.sourcesPtr

structure CheckLI (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends EarlyLI P g F s ra lo locals t where
  r10 : t.regs.r10.toBitVec = g.p.tgt
  r11 : t.regs.r11.toBitVec = g.p.n

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo locals : List Word}

theorem EarlyLI.toLoopLI (h : EarlyLI P g F s ra lo locals t) :
    LoopLI P g F s ra lo locals t :=
  ⟨h.toBd, h.rbx, h.r12, h.r15, h.r14, h.sources⟩

theorem LoopLI.next (h : LoopLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (_hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) : LoopLI P g F s ra lo locals u :=
  ⟨h.toBd.next hm hsp, hbx ▸ h.rbx, h12 ▸ h.r12, h15 ▸ h.r15,
    h14 ▸ h.r14, h.sources⟩

theorem EarlyLI.next (h : EarlyLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) : EarlyLI P g F s ra lo locals u :=
  ⟨h.toBd.next hm hsp, hbx ▸ h.rbx, h12 ▸ h.r12, h15 ▸ h.r15,
    hbp ▸ h.rbp, h14 ▸ h.r14, h.sources⟩

theorem CheckLI.next (h : CheckLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) (h10 : u.regs.r10 = t.regs.r10)
    (h11 : u.regs.r11 = t.regs.r11) : CheckLI P g F s ra lo locals u :=
  ⟨h.toEarlyLI.next hm hsp hbx h12 h15 hbp h14, h10 ▸ h.r10, h11 ▸ h.r11⟩

end

def CheckHead (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.n ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t)

def CheckNext (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.n ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t + 1)

def CheckDone (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, EarlyLI P g F s ra lo locals t ∧ Flat.targetsFrom g.p.fl g.spills 0 = true

theorem succ_lt {i n : Word} (hi : i < n) (hne : 1#64 + i ≠ n) : 1#64 + i < n := by
  bv_omega

end Bbu.Unit.PlannerRunU
