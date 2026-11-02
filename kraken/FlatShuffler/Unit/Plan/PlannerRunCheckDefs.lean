module

public import FlatShuffler.Unit.Plan.PlannerRunStore
import all FlatShuffler.Unit.Plan.PlannerRunStore
public import FlatShuffler.Unit.Plan.PlannerRunModel
import all FlatShuffler.Unit.Plan.PlannerRunModel

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU

structure LoopLI (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends Bd P g F s ra lo locals t where
  rbx : t.regs.rbx.toBitVec = P
  r14 : t.regs.r14.toBitVec = g.dataPtr
  ops : locals[1]? = some g.opsPtr
  strategy : locals[0]?.map (fun w => w.extractLsb' 56 8) = some ((rsi s).setWidth 8)
  sources : locals[2]? = some g.sourcesPtr

structure EarlyLI (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends Bd P g F s ra lo locals t where
  rbx : t.regs.rbx.toBitVec = P
  r14 : t.regs.r14.toBitVec = g.dataPtr
  ops : locals[1]? = some g.opsPtr
  rbp : t.regs.rbp.toBitVec = g.countPtr
  strategy : locals[0]?.map (fun w => w.extractLsb' 56 8) = some ((rsi s).setWidth 8)
  sources : r8 t = g.sourcesPtr

structure CheckLI (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop extends EarlyLI P g F s ra lo locals t where
  r10 : t.regs.r10.toBitVec = g.p.tgt
  r11 : t.regs.r11.toBitVec = g.p.n

section
variable {P : Addr} {g : PlannerCallMemory} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo locals : List Word}

theorem EarlyLI.toLoopLI (h : EarlyLI P g F s ra lo locals t)
    (hsrc : locals[2]? = some g.sourcesPtr) :
    LoopLI P g F s ra lo locals t :=
  ⟨h.toBd, h.rbx, h.r14, h.ops, h.strategy, hsrc⟩

theorem LoopLI.next (h : LoopLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (_h13 : u.regs.r13 = t.regs.r13) (_hbp : u.regs.rbp = t.regs.rbp)
    (_h12 : u.regs.r12 = t.regs.r12) : LoopLI P g F s ra lo locals u :=
  ⟨h.toBd.next hm hsp, hbx ▸ h.rbx, h14 ▸ h.r14, h.ops,
    h.strategy, h.sources⟩

theorem EarlyLI.next (h : EarlyLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h8 : u.regs.r8 = t.regs.r8) (hbp : u.regs.rbp = t.regs.rbp)
    (_h12 : u.regs.r12 = t.regs.r12) : EarlyLI P g F s ra lo locals u :=
  ⟨h.toBd.next hm hsp, hbx ▸ h.rbx, h14 ▸ h.r14, h.ops,
    hbp ▸ h.rbp, h.strategy, by simpa only [r8, Reg64s.get64_r8, h8] using h.sources⟩

theorem CheckLI.next (h : CheckLI P g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h8 : u.regs.r8 = t.regs.r8) (hbp : u.regs.rbp = t.regs.rbp)
    (_h12 : u.regs.r12 = t.regs.r12) (h10 : u.regs.r10 = t.regs.r10)
    (h11 : u.regs.r11 = t.regs.r11) : CheckLI P g F s ra lo locals u :=
  ⟨h.toEarlyLI.next hm hsp hbx h14 h8 hbp _h12, h10 ▸ h.r10, h11 ▸ h.r11⟩

theorem LoopLI.opsRead (h : LoopLI P g F s ra lo locals t) :
    rd t.dmem (t.regs.rsp.toBitVec + 8#64) = g.opsPtr := by
  have he := h.ops
  rw [List.getElem?_eq_getElem (by rw [h.localLength]; decide)] at he
  exact (h.localRead (i := 1) (by decide)).trans (Option.some.inj he)

theorem LoopLI.strategyRead (h : LoopLI P g F s ra lo locals t) :
    rdb t.dmem (t.regs.rsp.toBitVec + 7#64) = (rsi s).setWidth 8 := by
  have he := h.strategy
  simp only [List.getElem?_eq_getElem (by rw [h.localLength]; decide : 0 < locals.length),
    Option.map_some, Option.some.injEq] at he
  simpa only [Nat.reduceMul, BitVec.add_zero] using
    (h.localByteRead (i := 0) (j := 7) (by decide) (by decide)).trans he

end

def CheckHead (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.n ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t)

def CheckNext (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.n ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t + 1)

def CheckDone (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, EarlyLI P g F s ra lo locals t ∧ Flat.targetsFrom g.p.fl g.spills 0 = true

theorem succ_lt {i n : Word} (hi : i < n) (hne : 1#64 + i ≠ n) : 1#64 + i < n := by
  bv_omega

end FlatShuffler.Unit.PlannerRunU
