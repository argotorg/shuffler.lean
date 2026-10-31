import BbuKraken.Unit.Plan.PlannerRunEmissionHeader
import BbuKraken.Unit.Plan.PlannerRunCopy

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem AttemptLI.storeData (h : AttemptLI P g M F s ra lo locals t)
    {i : Word} (hi : i.toNat < MAX_N) (hcap : i.toNat < g.dataCapacity) (w : Word)
    (hm : u.dmem = t.dmem.storeInt (slotAt g.dataPtr i.toNat) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h15 : u.regs.r15 = t.regs.r15) (hbp : u.regs.rbp = t.regs.rbp)
    (h14 : u.regs.r14 = t.regs.r14) (h13 : u.regs.r13 = t.regs.r13) :
    AttemptLI P { g with data := Flat.put g.data i w } M F s ra lo locals u := by
  have hnew := store_data h.kb.vmem hi hcap w
  refine ⟨⟨⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, h.localLength⟩,
    hbx ▸ h.rbx, h12 ▸ h.r12, h15 ▸ h.r15, h14 ▸ h.r14,
    h.sources⟩, h.count, h.mapping, h.mappingEq, by rw [h13, hsp]; exact h.r13⟩
  rw [hm]
  exact (sep_lc _ _ _).symm ▸ hnew

theorem data_ok (hok : g.Ok) (v : Vector Word MAX_N) : ({g with data := v}).Ok :=
  ⟨hok.planner, hok.spillCount, hok.sourceIds, hok.targetIds, hok.ops, hok.traceLength⟩

theorem data_copy_step {wanted : Vector StackSlot MAX_N} {i : Word}
    (h : Flat.copyFrom g.p.fl i (g.data.map StackSlot.ofWord) = wanted)
    (hi : i < g.p.m) (w : Word)
    (hw : StackSlot.ofWord w = Flat.get g.p.fl.source i) :
    Flat.copyFrom g.p.fl (i + 1#64)
      ((Flat.put g.data i w).map StackSlot.ofWord) = wanted := by
  rw [copy_next hi] at h
  simp only [Flat.put, Vector.map_setIfInBounds, hw] at ⊢
  exact h

end

def EmitDataHead (P : Addr) (g : PlannerRunG) (M : Flat.Mapping) (F : MProp 64)
    (s : MachineData) (ra : Int64) (wanted : Vector StackSlot MAX_N) (t : MachineData) : Prop :=
  ∃ lo locals, AttemptLI P g M F s ra lo locals t ∧ rax t < g.p.m ∧
    Flat.copyFrom g.p.fl (rax t) (g.data.map StackSlot.ofWord) = wanted

end Bbu.Unit.PlannerRunU
