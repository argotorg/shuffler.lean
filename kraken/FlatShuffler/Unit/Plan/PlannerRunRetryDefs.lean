module

public import FlatShuffler.Unit.Plan.PlannerRunOutputDefs
import all FlatShuffler.Unit.Plan.PlannerRunOutputDefs
public import FlatShuffler.Unit.Plan.PlannerRunPrepare
import all FlatShuffler.Unit.Plan.PlannerRunPrepare

public import FlatShuffler.Unit.Memory
import all FlatShuffler.Unit.Memory

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

structure RetryLI (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData) : Prop
    extends PostEmitLI P g M F s ra lo locals t where
  targets : Flat.targetsFrom g.p.fl g.spills 0 = true

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem RetryLI.next (h : RetryLI P g M F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) : RetryLI P g M F s ra lo locals u :=
  ⟨h.toPostEmitLI.next hm hsp hbx h14 h15, h.targets⟩

theorem RetryLI.prepare (h : RetryLI P g M F s ra lo locals t) :
    PrepareHead P g F s ra t :=
  ⟨lo, locals, h.toLoopLI, h.r15, h.count, h.targets⟩

theorem dropped_read (h : (plannerCallOwnedMemory P g ∗ F).get t.dmem)
    {i : Word} (hi : i.toNat < maxStackSize) (hm : i.toNat < g.p.sourceSize.toNat) :
    ∃ R, (B8 (g.p.drp + i) (get g.dropped i) ∗ R).get t.dmem := by
  obtain ⟨R, hd⟩ := dropped h
  obtain ⟨Q, he, _⟩ := Bs.focus g.p.drp (g.dropped.toList.take g.p.sourceSize.toNat) (i := i.toNat)
    (by simp only [List.length_take, Vector.length_toList]; omega) 0#8
  rw [he, MProp.sep_assoc] at hd
  refine ⟨Q ∗ R, ?_⟩
  simpa only [List.getElem_take, Vector.getElem_toList, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Flat.get_toNat g.dropped hi] using hd

end

def DropBeforeHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals i, RetryLI P g M F s ra lo locals t ∧ i < g.p.sourceSize ∧
    rax t = g.p.drp + i ∧ rdx t = g.p.drp + g.p.sourceSize ∧
    Flat.droppedFrom g.p.sourceSize g.dropped i t.regs.rbp.toBitVec = Flat.droppedCount g.p.sourceSize g.dropped

def ResolveHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, RetryLI P g M F s ra lo locals t ∧
    t.regs.rbp.toBitVec = Flat.droppedCount g.p.sourceSize g.dropped

def DropAfterHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (before : Word) (t : MachineData) : Prop :=
  ∃ lo locals i, RetryLI P g M F s ra lo locals t ∧ i < g.p.sourceSize ∧
    rax t = g.p.drp + i ∧ rcx t = g.p.drp + g.p.sourceSize ∧ t.regs.rbp.toBitVec = before ∧
    Flat.droppedFrom g.p.sourceSize g.dropped i (rdx t) = Flat.droppedCount g.p.sourceSize g.dropped

end FlatShuffler.Unit.PlannerRunU
