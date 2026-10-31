import BbuKraken.Unit.Plan.PlannerRunFrame
import BbuKraken.Unit.Plan.PlannerRunMem

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo locals : List Word}

theorem Bd.localFocus (h : Bd P g F s ra lo locals t) :
    ∃ R, ∀ xs : List Word, xs.length = 4121 →
      Stk (rsp s) (fr s lo xs) ra.toBitVec ∗ (PlannerRunView P g ∗ F) =
        Arr t.regs.rsp.toBitVec xs ∗ R := by
  refine ⟨Arr (t.regs.rsp.toBitVec - 32904#64) lo ∗
    Arr (t.regs.rsp.toBitVec + 32968#64) (saved s) ∗
    Wd (rsp s - 8#64) ra.toBitVec ∗ (PlannerRunView P g ∗ F), ?_⟩
  intro xs hl
  have hs : (saved s).length = 6 := rfl
  simp only [Stk, fr, List.length_append, h.low, hl, hs, Nat.reduceAdd, Nat.reduceMul]
  rw [Arr.append, Arr.append]
  have ha : rsp s - 8#64 - 65920#64 = t.regs.rsp.toBitVec - 32904#64 := by
    rw [h.kb.sp]
    bv_omega
  have hb : t.regs.rsp.toBitVec - 32904#64 + 32904#64 = t.regs.rsp.toBitVec := by
    bv_omega
  simp only [h.low, hl, Nat.reduceMul, ha, hb]
  simp only [MProp.sep_assoc]
  exact sep_lc _ _ _

theorem Bd.localRead (h : Bd P g F s ra lo locals t) {i : Nat} (hi : i < 4121) :
    rd t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) =
      locals[i]'(h.localLength ▸ hi) := by
  obtain ⟨R, e⟩ := h.localFocus
  exact Arr.rd (e locals h.localLength ▸ h.kb.mem) (h.localLength ▸ hi)

theorem Bd.localSome (h : Bd P g F s ra lo locals t) {i : Nat} (hi : i < 4121) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  obtain ⟨R, e⟩ := h.localFocus
  exact Arr.isSome (e locals h.localLength ▸ h.kb.mem) (h.localLength ▸ hi)

theorem Bd.storeLocal (h : Bd P g F s ra lo locals t) {i : Nat} (hi : i < 4121)
    (w : Word) (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp) :
    Bd P g F s ra lo (locals.set i w) u := by
  obtain ⟨R, e⟩ := h.localFocus
  have hmem := e locals h.localLength ▸ h.kb.mem
  have hnew := Arr.store hmem (h.localLength ▸ hi) w
  have hl : (locals.set i w).length = 4121 := by simp [h.localLength]
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, hl⟩
  rw [hm, e _ hl]
  exact hnew

theorem Bd.storeSaw (h : Bd P g F s ra lo locals t) (x : Int)
    (hm : u.dmem = t.dmem.storeInt (P + 56#64) 1 x)
    (hsp : u.regs.rsp = t.regs.rsp) :
    Bd P (withSaw g (BitVec.ofInt 8 x)) F s ra lo locals u := by
  have hmem : (PlannerRunView P g ∗ (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F)).get t.dmem :=
    (sep_lc _ _ _) ▸ h.kb.mem
  have hnew := store_saw hmem x
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, h.localLength⟩
  rw [hm]
  exact (sep_lc _ _ _).symm ▸ hnew

end
end Bbu.Unit.PlannerRunU
