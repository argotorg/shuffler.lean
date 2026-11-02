module

public import FlatShuffler.Unit.Plan.PlannerRunCheckDefs
import all FlatShuffler.Unit.Plan.PlannerRunCheckDefs

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU

def CheckScan (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.targetSize ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t) ∧
    (rsi t).setWidth 8 = (Flat.get g.p.fl.target (rcx t)).kind ∧
    (isJunk (Flat.get g.p.fl.target (rcx t)) ||
      canBeFreelyGenerated (Flat.get g.p.fl.target (rcx t))) = false ∧
    rdi t = g.p.sourceSize ∧ t.regs.r15.toBitVec = g.p.src ∧
    StackSlot.ofWord (r9 t) = Flat.get g.p.fl.target (rcx t) ∧ rax t < g.p.sourceSize ∧
    Flat.containsFrom g.p.fl.source g.p.sourceSize (Flat.get g.p.fl.target (rcx t)) 0 =
      Flat.containsFrom g.p.fl.source g.p.sourceSize (Flat.get g.p.fl.target (rcx t)) (rax t)

def CheckMissing (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, CheckLI P g F s ra lo locals t ∧ rcx t < g.p.targetSize ∧
    Flat.targetsFrom g.p.fl g.spills 0 = Flat.targetsFrom g.p.fl g.spills (rcx t) ∧
    (rsi t).setWidth 8 = (Flat.get g.p.fl.target (rcx t)).kind ∧
    (isJunk (Flat.get g.p.fl.target (rcx t)) ||
      canBeFreelyGenerated (Flat.get g.p.fl.target (rcx t))) = false ∧
    Flat.containsFrom g.p.fl.source g.p.sourceSize (Flat.get g.p.fl.target (rcx t)) 0 = false

end FlatShuffler.Unit.PlannerRunU
