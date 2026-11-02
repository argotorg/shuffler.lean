module

public import FlatShuffler.Unit.Plan.ResolveWorkModel
import all FlatShuffler.Unit.Plan.ResolveWorkModel

@[expose] public section

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

def SpillReady (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L, Core P r F s ra w lo L t ∧ w.Model r s ∧
    t.regs.r15.toBitVec = (w.pick r).1 ∧ L.bestClass = (w.pick r).2 ∧
    (w.pick r).1 ≠ Flat.NONE ∧ (w.pick r).2 = Flat.SPILL

def DropReady (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ w lo L best, Core P r F s ra w lo L t ∧ t.regs.r15.toBitVec = best ∧
    best < r.p.sourceSize ∧ (w.drop best).Model r s

def dropPhase (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (l : Label) (t : MachineData) : Prop :=
  if l = ".LB.Planner.resolve.13" then DropReady P r F s ra t
  else if l = ".LB.Planner.resolve.14" then SpillReady P r F s ra t
  else rest l t

end FlatShuffler.Unit.ResolveU
