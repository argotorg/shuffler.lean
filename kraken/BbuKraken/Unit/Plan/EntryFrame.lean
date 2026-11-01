module

public import BbuKraken.Unit.Plan.EntryDefs
import all BbuKraken.Unit.Plan.EntryDefs

@[expose] public section

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

section
variable {g : EG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo locals : List Word}

theorem Bd.next (h : Bd g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) : Bd g F s ra lo locals u :=
  ⟨h.kb.next hm hsp, h.low, h.localLength, hbp.trans h.bp,
    h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem LI.next (h : LI g F s ra lo locals t)
    (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15)
    (hdi : u.regs.rdi = t.regs.rdi) (hsi : u.regs.rsi = t.regs.rsi)
    (hdx : u.regs.rdx = t.regs.rdx) (hcx : u.regs.rcx = t.regs.rcx)
    (h8 : u.regs.r8 = t.regs.r8) (h9 : u.regs.r9 = t.regs.r9)
    (hbx : u.regs.rbx = t.regs.rbx) (h11 : u.regs.r11 = t.regs.r11) :
    LI g F s ra lo locals u :=
  ⟨h.toBd.next hm hsp hbp h12 h13 h14 h15,
    hdi ▸ h.rdi, hsi ▸ h.rsi, hdx ▸ h.rdx, hcx ▸ h.rcx,
    h8 ▸ h.r8, h9 ▸ h.r9, hbx ▸ h.rbx, h11 ▸ h.r11⟩

theorem Bd.mem (h : Bd g F s ra lo locals t) :
    (View (rsp s) g ∗ (Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ F)).get t.dmem :=
  (sep_lc _ _ _) ▸ h.kb.mem

theorem Bd.localFocus (h : Bd g F s ra lo locals t) :
    ∃ R, ∀ xs : List Word, xs.length = 10 →
      Stk (rsp s) (fr s lo xs) ra.toBitVec ∗ (View (rsp s) g ∗ F) =
        Arr t.regs.rsp.toBitVec xs ∗ R := by
  refine ⟨Arr (t.regs.rsp.toBitVec - 65928#64) lo ∗
    Wd (t.regs.rsp.toBitVec + 80#64) s.regs.rbx.toBitVec ∗
    Wd (rsp s - 8#64) ra.toBitVec ∗ (View (rsp s) g ∗ F), ?_⟩
  intro xs hl
  simp only [Stk, fr, List.length_append, h.low, hl, List.length_singleton,
    Nat.reduceAdd, Nat.reduceMul, Arr.append, Arr, MProp.sep_emp]
  have ha : rsp s - 8#64 - 66016#64 = t.regs.rsp.toBitVec - 65928#64 := by
    rw [h.kb.sp]
    bv_omega
  have hb : t.regs.rsp.toBitVec - 65928#64 + 65928#64 = t.regs.rsp.toBitVec := by
    bv_omega
  simp only [ha, hb, MProp.sep_assoc]
  exact sep_lc _ _ _

theorem Bd.localRead (h : Bd g F s ra lo locals t) {i : Nat} (hi : i < 10) :
    rd t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) =
      locals[i]'(h.localLength ▸ hi) := by
  obtain ⟨R, he⟩ := h.localFocus
  exact Arr.rd (he locals h.localLength ▸ h.kb.mem) (h.localLength ▸ hi)

theorem Bd.localSome (h : Bd g F s ra lo locals t) {i : Nat} (hi : i < 10) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  obtain ⟨R, he⟩ := h.localFocus
  exact Arr.isSome (he locals h.localLength ▸ h.kb.mem) (h.localLength ▸ hi)

theorem Bd.storeLocal (h : Bd g F s ra lo locals t) {i : Nat} (hi : i < 10) (w : Word)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) : Bd g F s ra lo (locals.set i w) u := by
  obtain ⟨R, he⟩ := h.localFocus
  have hnew := Arr.store (he locals h.localLength ▸ h.kb.mem) (h.localLength ▸ hi) w
  have hl : (locals.set i w).length = 10 := by simp [h.localLength]
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.low, hl, hbp.trans h.bp,
    h12.trans h.r12, h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩
  rw [hm, he _ hl]
  exact hnew

end
end Bbu.Unit.EntryValidU
