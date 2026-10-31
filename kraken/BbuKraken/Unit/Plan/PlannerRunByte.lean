import BbuKraken.Unit.Plan.PlannerRunStore
import BbuKraken.Unit.Plan.ResolveByteFrame

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem Bd.storeLocalByte {P : Addr} {g : PlannerRunG} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}
    (h : Bd P g F s ra lo locals t) {i : Nat} (hi : i < 4121)
    {j : Word} (hj : j.toNat < 8) (z : Int)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) + j) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp) :
    ∃ w : Word, Bd P g F s ra lo (locals.set i w) u := by
  obtain ⟨R, e⟩ := h.localFocus
  obtain ⟨Q, he, hs⟩ := ResolveU.Arr_focus_set
    t.regs.rsp.toBitVec locals (h.localLength ▸ hi)
  have hm0 := e locals h.localLength ▸ h.kb.mem
  rw [he, MProp.sep_assoc] at hm0
  obtain ⟨w, hw⟩ := ResolveU.Wd_storeByte hm0 hj z
  have hl : (locals.set i w).length = 4121 := by simp [h.localLength]
  refine ⟨w, ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, hl⟩⟩
  rw [hm, e _ hl, hs w, MProp.sep_assoc]
  exact hw

end Bbu.Unit.PlannerRunU
