module

public import BbuKraken.Unit.Plan.PlannerRunOutputDefs
import all BbuKraken.Unit.Plan.PlannerRunOutputDefs
public import BbuKraken.Unit.Plan.PlannerRunPrepare
import all BbuKraken.Unit.Plan.PlannerRunPrepare
public import BbuKraken.Unit.SpillSetLemmas
import all BbuKraken.Unit.SpillSetLemmas

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

structure RetryLI (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (lo locals : List Word) (t : MachineData) : Prop
    extends PostEmitLI P g M F s ra lo locals t where
  targets : Flat.targetsFrom g.p.fl g.spills 0 = true

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem RetryLI.next (h : RetryLI P g M F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) : RetryLI P g M F s ra lo locals u :=
  ⟨h.toPostEmitLI.next hm hsp hbx h12 h15 h14 h13, h.targets⟩

theorem RetryLI.prepare (h : RetryLI P g M F s ra lo locals t) :
    PrepareHead P g F s ra t :=
  ⟨lo, locals, h.toLoopLI, h.r13, h.count, h.targets⟩

theorem dropped_read (h : (PlannerRunView P g ∗ F).get t.dmem)
    {i : Word} (hi : i.toNat < MAX_N) (hm : i.toNat < g.p.m.toNat) :
    ∃ R, (B8 (g.p.drp + i) (get g.dropped i) ∗ R).get t.dmem := by
  obtain ⟨R, hd⟩ := dropped h
  obtain ⟨Q, he, _⟩ := SpillSetProof.Bs.focus g.p.drp (g.dropped.toList.take g.p.m.toNat) (i := i.toNat)
    (by simp only [List.length_take, Vector.length_toList]; omega) 0#8
  rw [he, MProp.sep_assoc] at hd
  refine ⟨Q ∗ R, ?_⟩
  simpa only [List.getElem_take, Vector.getElem_toList, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Flat.get_toNat g.dropped hi] using hd

end

def DropBeforeHead (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals i, RetryLI P g M F s ra lo locals t ∧ i < g.p.m ∧
    rax t = g.p.drp + i ∧ rdx t = g.p.drp + g.p.m ∧
    Flat.droppedFrom g.p.m g.dropped i t.regs.rbp.toBitVec = Flat.droppedCount g.p.m g.dropped

def ResolveHead (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ lo locals, RetryLI P g M F s ra lo locals t ∧
    t.regs.rbp.toBitVec = Flat.droppedCount g.p.m g.dropped

def DropAfterHead (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (before : Word) (t : MachineData) : Prop :=
  ∃ lo locals i, RetryLI P g M F s ra lo locals t ∧ i < g.p.m ∧
    rax t = g.p.drp + i ∧ rcx t = g.p.drp + g.p.m ∧ t.regs.rbp.toBitVec = before ∧
    Flat.droppedFrom g.p.m g.dropped i (rdx t) = Flat.droppedCount g.p.m g.dropped

end Bbu.Unit.PlannerRunU
