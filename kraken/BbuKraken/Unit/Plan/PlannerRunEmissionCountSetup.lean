module

public import BbuKraken.Unit.Plan.PlannerRunEmissionDefs
import all BbuKraken.Unit.Plan.PlannerRunEmissionDefs
public import BbuKraken.Unit.Run.Model
import all BbuKraken.Unit.Run.Model

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

def setupLocals (locals : List Word) (sp : Addr) : List Word :=
  (locals.set 4115 0#64).set 4118 (sp + 96#64)

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}

theorem EmitLI.setupCount (h : EmitLI P g M F s ra lo locals t) (hok : g.Ok)
    (hd : WordPrefix locals 2067 M.dest g.p.m.toNat)
    (hp : WordPrefix locals 3091 M.pos g.p.n.toNat)
    (hm : u.dmem = (t.dmem.storeInt (t.regs.rsp.toBitVec + 32920#64) 8 0).storeInt
      (t.regs.rsp.toBitVec + 32944#64) 8 (t.regs.rsp.toBitVec + 96#64).toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbx : u.regs.rbx = t.regs.rbx) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13 = t.regs.r13) (hbp : u.regs.rbp = t.regs.rbp)
    (h12 : u.regs.r12 = t.regs.r12) (h15 : u.regs.r15 = t.regs.r15) :
    EmitCountLI P g M F s ra lo (setupLocals locals t.regs.rsp.toBitVec) u := by
  let v : MachineData := { t with dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + 32920#64) 8 0 }
  have h1 : EmitLI P g M F s ra lo (locals.set 4115 0#64) v :=
    h.storeLocal hok (by decide) (by decide) 0#64 rfl rfl rfl rfl rfl rfl rfl rfl
  have h2 : EmitLI P g M F s ra lo (setupLocals locals t.regs.rsp.toBitVec) u :=
    h1.storeLocal hok (by decide) (by decide) (t.regs.rsp.toBitVec + 96#64)
      hm hsp hbx h14 h13 hbp h12 h15
  have hout (base count : Nat) (hb : base + count ≤ 4115) (v : Vector Word MAX_N)
      (hh : WordPrefix locals base v count) :
      WordPrefix (setupLocals locals t.regs.rsp.toBitVec) base v count :=
    (hh.set_outside (by intro i hi; omega) 0#64).set_outside
      (by intro i hi; omega) (t.regs.rsp.toBitVec + 96#64)
  refine ⟨h2, hout 2067 _ ?_ _ hd, hout 3091 _ ?_ _ hp, ?_⟩
  · have hm := hok.planner.m
    change g.p.m.toNat ≤ 1024 at hm
    omega
  · have hn := hok.planner.n
    change g.p.n.toNat ≤ 1024 at hn
    omega
  · rw [setupLocals, hsp]
    exact List.getElem?_set_self (by simp [h.localLength])

theorem setupLocals.pending (hl : locals.length = 4121) (sp : Addr) :
    (setupLocals locals sp)[4115]? = some 0#64 := by
  simp only [setupLocals, List.getElem?_set, show (4118:Nat) ≠ 4115 by decide,
    ↓reduceIte, show 4115 < locals.length by omega, ↓reduceIte]

end
end Bbu.Unit.PlannerRunU
