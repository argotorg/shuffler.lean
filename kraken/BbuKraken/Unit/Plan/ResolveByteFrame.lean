module

public import BbuKraken.Unit.Plan.ResolveBytes
import all BbuKraken.Unit.Plan.ResolveBytes

@[expose] public section

namespace Bbu.Unit.ResolveU
open Bbu.Sep

-- A byte store changes one word. The rest of the word array is the same.
theorem Arr_focus_set (a : Addr) (ws : List Word) {i : Nat} (hi : i < ws.length) :
    ∃ R, Arr a ws = Wd (a + BitVec.ofNat 64 (8 * i)) ws[i] ∗ R ∧
      ∀ w, Arr a (ws.set i w) = Wd (a + BitVec.ofNat 64 (8 * i)) w ∗ R := by
  induction ws generalizing a i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero => exact ⟨Arr (a + 8#64) ws, by simp [Arr], fun _ => by simp [Arr]⟩
    | succ i =>
      obtain ⟨R, he, hs⟩ := ih (a + 8#64) (by simpa using hi)
      have ha : a + 8#64 + BitVec.ofNat 64 (8 * i) =
          a + BitVec.ofNat 64 (8 * (i + 1)) := by
        simp only [Nat.mul_add, BitVec.ofNat_add]
        bv_omega
      refine ⟨Wd a w ∗ R, ?_, fun x => ?_⟩
      · simp only [Arr, List.getElem_cons_succ]
        rw [he, ha, sep_lc]
      · simp only [Arr, List.set_cons_succ]
        rw [hs, ha, sep_lc]

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo loc : List Word}

theorem Bd.storeLocalByte (h : Bd P r F s ra lo loc t) {i : Nat} (hi : i < loc.length)
    {j : Word} (hj : j.toNat < 8) (z : Int)
    (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) + j) 1 z)
    (hsp : u.regs.rsp = t.regs.rsp) :
    ∃ w : Word, Bd P r F s ra lo (loc.set i w) u := by
  have hi' : lo.length + i < (fr s lo loc).length := by simp [fr, saved]; omega
  have ha : rsp s - 8#64 - BitVec.ofNat 64 (8 * (fr s lo loc).length)
      + BitVec.ofNat 64 (8 * (lo.length + i)) =
        t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) := by
    rw [h.fr_len, resolveD, h.free, h.kb.sp]
    simp only [Nat.mul_add, BitVec.ofNat_add]
    bv_omega
  have hset : ∀ w, (fr s lo loc).set (lo.length + i) w = fr s lo (loc.set i w) := by
    intro w
    rw [fr, List.set_append_right (s := lo) (t := loc ++ saved s) _ _ (by omega),
      Nat.add_sub_cancel_left, List.set_append_left _ _ hi]
    rfl
  obtain ⟨R, he, hs⟩ := Arr_focus_set
    (rsp s - 8#64 - BitVec.ofNat 64 (8 * (fr s lo loc).length)) (fr s lo loc) hi'
  have hm0 := h.kb.mem
  unfold Stk at hm0
  rw [he, MProp.sep_assoc, ha] at hm0
  simp only [MProp.sep_assoc] at hm0
  obtain ⟨w, hmw⟩ := Wd_storeByte hm0 hj z
  have hew : Stk (rsp s) (fr s lo (loc.set i w)) ra.toBitVec ∗ (RView P r ∗ F) =
      Wd (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) w ∗
        (R ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ (RView P r ∗ F)) := by
    rw [← hset w]
    unfold Stk
    rw [List.length_set, hs w, ha, MProp.sep_assoc]
    rw [MProp.sep_assoc]
  refine ⟨w, ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.free, by simpa using h.locals⟩⟩
  rw [hm, hew]
  exact hmw

theorem Bd.zeroByteSome (h : Bd P r F s ra lo loc t) {o : Word} (ho : o.toNat < MAX_N) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8240#64 + o) 1).isSome = true := by
  change o.toNat < 1024 at ho
  let i := 1030 + o.toNat / 8
  have hi : i < loc.length := by rw [h.locals]; change 1030 + o.toNat / 8 < 1159; omega
  obtain ⟨R, hm⟩ := h.localWord i hi
  have he : t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (o.toNat % 8) =
      t.regs.rsp.toBitVec + 8240#64 + o := by
    have hn : 8 * i + o.toNat % 8 = 8240 + o.toNat := by dsimp [i]; omega
    have hc : BitVec.ofNat 64 o.toNat = o := by simp
    simpa only [BitVec.ofNat_add, hc, BitVec.add_assoc] using
      congrArg (fun n => t.regs.rsp.toBitVec + BitVec.ofNat 64 n) hn
  rw [← he]
  exact Wd.isSome_byte hm (by omega)

theorem Bd.storeZeroByte (h : Bd P r F s ra lo loc t) {o : Word} (ho : o.toNat < MAX_N)
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec + 8240#64 + o) 1 0)
    (hsp : u.regs.rsp = t.regs.rsp) :
    ∃ w : Word, Bd P r F s ra lo (loc.set (1030 + o.toNat / 8) w) u := by
  change o.toNat < 1024 at ho
  let i := 1030 + o.toNat / 8
  have hi : i < loc.length := by rw [h.locals]; change 1030 + o.toNat / 8 < 1159; omega
  have he : t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (o.toNat % 8) =
      t.regs.rsp.toBitVec + 8240#64 + o := by
    have hn : 8 * i + o.toNat % 8 = 8240 + o.toNat := by dsimp [i]; omega
    have hc : BitVec.ofNat 64 o.toNat = o := by simp
    simpa only [BitVec.ofNat_add, hc, BitVec.add_assoc] using
      congrArg (fun n => t.regs.rsp.toBitVec + BitVec.ofNat 64 n) hn
  exact h.storeLocalByte hi (j := BitVec.ofNat 64 (o.toNat % 8))
    (by simp; omega) 0 (by rw [he]; exact hm) hsp

end
end Bbu.Unit.ResolveU
