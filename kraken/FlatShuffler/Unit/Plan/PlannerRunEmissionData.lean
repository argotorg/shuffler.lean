module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionHeader
import all FlatShuffler.Unit.Plan.PlannerRunEmissionHeader
public import FlatShuffler.Unit.Plan.PlannerRunCopy
import all FlatShuffler.Unit.Plan.PlannerRunCopy

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem AttemptLI.storeData (h : AttemptLI P g M F s ra lo locals t)
    {i : Word} (hi : i.toNat < maxStackSize) (hcap : i.toNat < g.dataCapacity) (w : Word)
    (hm : u.dmem = t.dmem.storeInt (slotAt g.dataPtr i.toNat) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (_h13 : u.regs.r13 = t.regs.r13) (_hbp : u.regs.rbp = t.regs.rbp)
    (_h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    AttemptLI P { g with data := Flat.put g.data i w } M F s ra lo locals u := by
  have hnew := store_data h.kb.vmem hi hcap w
  refine ⟨⟨⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, h.localLength⟩,
    hbx ▸ h.rbx, h14 ▸ h.r14, h.ops, h.strategy,
    h.sources⟩, h.count, h.mapping, h.mappingEq, by rw [h15, hsp]; exact h.r15⟩
  rw [hm]
  exact (sep_lc _ _ _).symm ▸ hnew

theorem data_ok (hok : g.Ok) (v : Vector Word maxStackSize) : ({g with data := v}).Ok :=
  ⟨hok.planner, hok.spillCount, hok.sourceIds, hok.targetIds, hok.ops, hok.traceLength⟩

theorem data_copy_step {wanted : Vector StackSlot maxStackSize} {i : Word}
    (h : Flat.copyFrom g.p.fl i (g.data.map StackSlot.ofWord) = wanted)
    (hi : i < g.p.sourceSize) (w : Word)
    (hw : StackSlot.ofWord w = Flat.get g.p.fl.source i) :
    Flat.copyFrom g.p.fl (i + 1#64)
      ((Flat.put g.data i w).map StackSlot.ofWord) = wanted := by
  rw [copy_next hi] at h
  simp only [Flat.put, Vector.map_setIfInBounds, hw] at ⊢
  exact h

end

def EmitDataHead (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (wanted : Vector StackSlot maxStackSize) (t : MachineData) : Prop :=
  ∃ lo locals, AttemptLI P g M F s ra lo locals t ∧ rax t < g.p.sourceSize ∧
    Flat.copyFrom g.p.fl (rax t) (g.data.map StackSlot.ofWord) = wanted

end FlatShuffler.Unit.PlannerRunU
