module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderFrame
import all FlatShuffler.Unit.Plan.PlannerRunBuilderFrame
public import FlatShuffler.Unit.Plan.ResolveByteFrame
import all FlatShuffler.Unit.Plan.ResolveByteFrame

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

private theorem low_sext (pad : BitVec 56) (x : BitVec 8) :
    (pad ++ x).signExtend 8 = x := by bv_decide

private theorem high_sext (pad : BitVec 56) (x : BitVec 8) :
    ((pad ++ x).sshiftRight 8).signExtend 56 = pad := by bv_decide

theorem word_lowByte (a : Addr) (pad : BitVec 56) :
    ∃ R, ∀ x : BitVec 8, Wd a (pad ++ x) = B8 a x ∗ R := by
  refine ⟨(Int.toBytes 7 pad.toInt).AtM (a + 1#64), fun x => ?_⟩
  unfold Wd B8
  rw [show Int.toBytes 8 (pad ++ x).toInt = Int.toBytes (1 + 7) (pad ++ x).toInt from rfl,
    toBytes_add, AtM_append _ _ _ (by simp [Int.toBytes_length])]
  simp only [Int.toBytes_length, ← BitVec.toInt_sshiftRight]
  rw [toBytes_sext 1, toBytes_sext 7, low_sext, high_sext]

theorem word_storeLowByte {a : Addr} {w : Word} {F : MProp 64} {m : Mem 64}
    (h : (Wd a w ∗ F).get m) (z : Int) :
    (Wd a (w.extractLsb' 8 56 ++ BitVec.ofInt 8 z) ∗ F).get (m.storeInt a 1 z) := by
  have hw : w = w.extractLsb' 8 56 ++ w.extractLsb' 0 8 := by bv_decide
  obtain ⟨R, he⟩ := word_lowByte a (w.extractLsb' 8 56)
  rw [hw, he, MProp.sep_assoc] at h
  have hs := B8.store h z
  rw [he, MProp.sep_assoc]
  exact hs

theorem Bd.storeLocalLowByte {P : Addr} {g : PlannerCallMemory} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals : List Word}
    (h : Bd P g F s ra lo locals t) {i : Nat} (hi : i < 4121) (z : Int)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp) :
    Bd P g F s ra lo
      (locals.set i ((locals[i]'(h.localLength ▸ hi)).extractLsb' 8 56 ++ BitVec.ofInt 8 z)) u := by
  obtain ⟨R, e⟩ := h.localFocus
  obtain ⟨Q, he, hs⟩ := ResolveU.Arr_focus_set
    t.regs.rsp.toBitVec locals (h.localLength ▸ hi)
  have hm0 := e locals h.localLength ▸ h.kb.mem
  rw [he, MProp.sep_assoc] at hm0
  have hm1 := word_storeLowByte hm0 z
  have hl : (locals.set i
      ((locals[i]'(h.localLength ▸ hi)).extractLsb' 8 56 ++ BitVec.ofInt 8 z)).length = 4121 := by
    simp [h.localLength]
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, hl⟩
  rw [hm, e _ hl, hs, MProp.sep_assoc]
  exact hm1

end FlatShuffler.Unit.PlannerRunU
