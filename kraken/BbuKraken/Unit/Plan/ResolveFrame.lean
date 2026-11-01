module

public import BbuKraken.Unit.Plan.ResolveMem
import all BbuKraken.Unit.Plan.ResolveMem

@[expose] public section

namespace Bbu.Unit.ResolveU

open Bbu.Sep

def saved (s : MachineData) : List Word :=
  [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
    s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

def fr (s : MachineData) (lo loc : List Word) : List Word := lo ++ (loc ++ saved s)

structure Bd (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo loc : List Word) (t : MachineData) : Prop where
  kb : Kb (RView P r ∗ F) s ra (fr s lo loc) 9320#64 t
  free : lo.length = 17
  locals : loc.length = 1159

section
variable {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo loc : List Word}

theorem Bd.next (h : Bd P r F s ra lo loc t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) : Bd P r F s ra lo loc u :=
  ⟨h.kb.next hm hsp, h.free, h.locals⟩

theorem Bd.hi_len (h : Bd P r F s ra lo loc t) :
    9320#64 = BitVec.ofNat 64 (8 * (loc ++ saved s).length) := by
  simp [h.locals, saved]

theorem Bd.fr_len (h : Bd P r F s ra lo loc t) : (fr s lo loc).length = resolveD := by
  simp [fr, h.free, h.locals, saved, resolveD]

theorem Bd.localWord (h : Bd P r F s ra lo loc t) (i : Nat) (hi : i < loc.length) :
    ∃ R, (Wd (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) loc[i] ∗ R).get t.dmem := by
  obtain ⟨R, hm⟩ := h.kb.arr_hi (lo := lo) (hi := loc ++ saved s) h.hi_len
  have hi' : i < (loc ++ saved s).length := by simp; omega
  obtain ⟨Q, e⟩ := Arr.focus t.regs.rsp.toBitVec (loc ++ saved s) hi'
  rw [e, MProp.sep_assoc, List.getElem_append_left hi] at hm
  exact ⟨_, hm⟩

theorem Bd.storeLocal (h : Bd P r F s ra lo loc t) {i : Nat} (hi : i < loc.length)
    (w : Word) (hm : u.dmem = t.dmem.storeInt
      (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8 w.toInt)
    (hsp : u.regs.rsp = t.regs.rsp) : Bd P r F s ra lo (loc.set i w) u := by
  have hj : lo.length + i < (fr s lo loc).length := by simp [fr, saved]; omega
  have ha : rsp s - 8#64 - BitVec.ofNat 64 (8 * (fr s lo loc).length)
      + BitVec.ofNat 64 (8 * (lo.length + i)) =
        t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) := by
    rw [h.fr_len, resolveD, h.free, h.kb.sp]
    simp only [Nat.mul_add, BitVec.ofNat_add]
    bv_omega
  have he : (fr s lo loc).set (lo.length + i) w = fr s lo (loc.set i w) := by
    rw [fr, List.set_append_right (s := lo) (t := loc ++ saved s) _ _ (by omega),
      Nat.add_sub_cancel_left, List.set_append_left _ _ hi]
    rfl
  have hv := h.kb.mem
  unfold Stk at hv
  rw [MProp.sep_assoc] at hv
  have hs := Arr.store hv hj w
  rw [he, ha] at hs
  refine ⟨⟨?_, hsp ▸ h.kb.sp⟩, h.free, by simpa using h.locals⟩
  rw [hm]
  simpa only [Stk, fr, List.length_append, List.length_set, MProp.sep_assoc] using hs

theorem Bd.popSome (h : Bd P r F s ra lo loc t) (i : Nat) (hi : i < 6) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 9272#64 + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  have e : t.regs.rsp.toBitVec + 9272#64 + BitVec.ofNat 64 (8 * i) =
      t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (loc.length + i)) := by
    rw [h.locals]
    simp only [Nat.mul_add, BitVec.ofNat_add]
    bv_omega
  rw [e]
  apply h.kb.isSome_hi (lo := lo) (hi := loc ++ saved s) h.hi_len
  simp only [List.length_append, saved, List.length_cons, List.length_nil]
  omega

theorem Bd.popWord (h : Bd P r F s ra lo loc t) (i : Nat) (hi : i < 6) :
    rd t.dmem (t.regs.rsp.toBitVec + 9272#64 + BitVec.ofNat 64 (8 * i)) =
      (saved s)[i]'(by simpa [saved] using hi) := by
  have e : t.regs.rsp.toBitVec + 9272#64 + BitVec.ofNat 64 (8 * i) =
      t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (loc.length + i)) := by
    rw [h.locals]
    simp only [Nat.mul_add, BitVec.ofNat_add]
    bv_omega
  rw [e]
  have hi' : loc.length + i < (loc ++ saved s).length := by simp [saved]; omega
  have hr := h.kb.rd_hi (lo := lo) (hi := loc ++ saved s) h.hi_len hi'
  rw [List.getElem_append_right (by omega)] at hr
  simpa using hr

theorem Bd.pop (h : Bd P r F s ra lo loc t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 9272#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 +
      8#64 + 8#64 + 8#64 + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (9272#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (9272#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : u.regs.r12.toBitVec = rd t.dmem (9272#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : u.regs.r13.toBitVec = rd t.dmem (9272#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : u.regs.r14.toBitVec = rd t.dmem (9272#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64))
    (h15 : u.regs.r15.toBitVec = rd t.dmem
      (9272#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)) :
    Kg (RView P r ∗ F) s ra (fr s lo loc) u := by
  simp only [BitVec.add_comm (9272#64) t.regs.rsp.toBitVec] at hsp hbx hbp h12 h13 h14 h15
  have hr := fun i (hi : i < 6) => h.popWord i hi
  simp only [BitVec.add_assoc, saved] at hr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbx hbp h12 h13 h14 h15
  refine h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals apply UInt64.toBitVec_inj.mp
  · exact hbx.trans (hr 0 (by decide))
  · exact hbp.trans (hr 1 (by decide))
  · exact h12.trans (hr 2 (by decide))
  · exact h13.trans (hr 3 (by decide))
  · exact h14.trans (hr 4 (by decide))
  · exact h15.trans (hr 5 (by decide))
end

theorem post_rax {r r' : RG} {s t u : MachineData} (h : resolveQ r r' s t)
    (ha : rax u = rax t) : resolveQ r r' s u := by
  intro v
  obtain ⟨hal, hq⟩ := h v
  exact ⟨(congrArg (BitVec.setWidth 8) ha).trans hal, hq⟩

end Bbu.Unit.ResolveU
