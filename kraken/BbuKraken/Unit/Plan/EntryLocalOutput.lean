import BbuKraken.Unit.Plan.EntryCallDefs
import BbuKraken.Unit.Plan.EntryOutput

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

private theorem low_byte (hi : BitVec 56) (lo : BitVec 8) :
    ((hi ++ lo).extractLsb' 0 8) = lo := by bv_decide

theorem Bd.callCount {g : EG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo : List Word} {l : CallLocals}
    (h : Bd g F s ra lo (l.toList g.r) t) :
    rd t.dmem (t.regs.rsp.toBitVec + 8#64) = g.r.count := by
  exact h.localRead (i := 1) (by decide)

theorem Bd.callSaw {g : EG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    {lo : List Word} {l : CallLocals}
    (h : Bd g F s ra lo (l.toList g.r) t) :
    rdb t.dmem (t.regs.rsp.toBitVec + 72#64) = g.r.p.saw := by
  obtain ⟨R, he⟩ := h.localFocus
  obtain ⟨Q, hf, _⟩ := ResolveU.Arr_focus_set t.regs.rsp.toBitVec (l.toList g.r)
    (show 9 < (l.toList g.r).length by simp [CallLocals.length])
  have hm := he (l.toList g.r) h.localLength ▸ h.kb.mem
  rw [hf, MProp.sep_assoc] at hm
  have hr := Wd.rdb_byte hm (j := 0) (by decide)
  simpa only [CallLocals.toList, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceMul, BitVec.add_zero, low_byte] using hr

end Bbu.Unit.EntryValidU
