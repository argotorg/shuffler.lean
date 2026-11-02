module

public import BbuKraken.Unit.Plan.PlannerRunCheckDefs
import all BbuKraken.Unit.Plan.PlannerRunCheckDefs

@[expose] public section

namespace Bbu.Unit.PlannerRunU

def CheckScan (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.n ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t) ∧
    (rsi t).setWidth 8 = (Flat.get g.p.fl.target (rcx t)).kind ∧
    (isJunk (Flat.get g.p.fl.target (rcx t)) ||
      canBeFreelyGenerated (Flat.get g.p.fl.target (rcx t))) = false ∧
    rdi t = g.p.m ∧ t.regs.r15.toBitVec = g.p.src ∧
    StackSlot.ofWord (r9 t) = Flat.get g.p.fl.target (rcx t) ∧ rax t < g.p.m ∧
    Flat.containsFrom g.p.fl.source g.p.m (Flat.get g.p.fl.target (rcx t)) 0 =
      Flat.containsFrom g.p.fl.source g.p.m (Flat.get g.p.fl.target (rcx t)) (rax t)

def CheckMissing (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.n ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t) ∧
    (rsi t).setWidth 8 = (Flat.get g.p.fl.target (rcx t)).kind ∧
    (isJunk (Flat.get g.p.fl.target (rcx t)) ||
      canBeFreelyGenerated (Flat.get g.p.fl.target (rcx t))) = false ∧
    Flat.containsFrom g.p.fl.source g.p.m (Flat.get g.p.fl.target (rcx t)) 0 = false

end Bbu.Unit.PlannerRunU
