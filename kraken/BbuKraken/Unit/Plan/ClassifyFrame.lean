module

public import BbuKraken.Unit.Plan.ClassifyMem
import all BbuKraken.Unit.Plan.ClassifyMem

@[expose] public section

namespace Bbu.Unit.ClassifyU
open Bbu.Sep

def saved (s : MachineData) : List Word :=
  [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
    s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

def fr (s : MachineData) (lo : List Word) (w q : Word) : List Word :=
  (lo ++ [w]) ++ q :: saved s

theorem split_frame {xs : List Word} (hl : xs.length = 16) :
    ∃ lo w q a b c d e f, xs = lo ++ [w, q, a, b, c, d, e, f] ∧ lo.length = 8 := by
  have hd : (xs.drop 8).length = 8 := by simp [hl]
  match he : xs.drop 8, hd with
  | [w, q, a, b, c, d, e, f], _ =>
    exact ⟨xs.take 8, w, q, a, b, c, d, e, f,
      by rw [← he, List.take_append_drop], by simp [hl]⟩

structure Bd (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (w q : Word) (t : MachineData) : Prop where
  kb : Kb (CView P c ∗ F) s ra (fr s lo w q) 56#64 t
  len : lo.length = 8

structure LI (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo : List Word) (w q : Word) (t : MachineData) : Prop extends Bd P c F s ra lo w q t where
  rbx : t.regs.rbx.toBitVec = P
  rbp : t.regs.rbp.toBitVec = rcx s
  r12 : t.regs.r12.toBitVec = c.h.mp
  r13 : t.regs.r13.toBitVec.extractLsb' 0 8 = (inp c s).slot.kind
  r14 : t.regs.r14.toBitVec = c.h.dn
  r15 : t.regs.r15.toBitVec = sw c s
  nonreturn : (inp c s).slot.kind ≠ FunctionReturnLabel
  locals : (inp c s).slot.kind ≠ Junk →
    q.extractLsb' 32 32 = (inp c s).slot.payload ∧
    q.extractLsb' 24 8 = (inp c s).slot.valueOpcode

section
variable {P : Addr} {c : CG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo : List Word} {w q : Word}

theorem Bd.next (h : Bd P c F s ra lo w q t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) : Bd P c F s ra lo w q u :=
  ⟨h.kb.next hm hsp, h.len⟩

theorem LI.next (h : LI P c F s ra lo w q t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) (hbx : u.regs.rbx = t.regs.rbx)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) : LI P c F s ra lo w q u :=
  ⟨h.toBd.next hm hsp, by rw [hbx]; exact h.rbx, by rw [hbp]; exact h.rbp,
    by rw [h12]; exact h.r12, by rw [h13]; exact h.r13, by rw [h14]; exact h.r14,
    by rw [h15]; exact h.r15, h.nonreturn, h.locals⟩

theorem LI.after {lo' : List Word} {w' : Word} (h : LI P c F s ra lo w q t)
    (hk : Kb (CView P c ∗ F) s ra (fr s lo' w' q) 56#64 u)
    (hl : lo'.length = 8) (hag : Sep.mod.Agree t u) : LI P c F s ra lo' w' q u :=
  ⟨⟨hk, hl⟩,
    by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]; exact h.rbx,
    by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.rbp,
    by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12,
    by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13]; exact h.r13,
    by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14,
    by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact h.r15,
    h.nonreturn, h.locals⟩

theorem Bd.localWord (h : Bd P c F s ra lo w q t) :
    ∃ R, (Wd t.regs.rsp.toBitVec q ∗ R).get t.dmem := by
  obtain ⟨R, hm⟩ := h.kb.arr_hi (lo := lo ++ [w]) (hi := q :: saved s) rfl
  simp only [Arr, MProp.sep_assoc] at hm
  exact ⟨_, hm⟩

theorem Bd.popSome (h : Bd P c F s ra lo w q t) :
    ∀ (i : Nat), i < 6 →
      (t.dmem.loadInt (8#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  intro i hi
  rw [show 8#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * i) =
    t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (i + 1)) by
      simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]; bv_omega]
  exact h.kb.isSome_hi (lo := lo ++ [w]) (hi := q :: saved s) rfl (by simp [saved]; omega)

theorem Bd.pop (h : Bd P c F s ra lo w q t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : u.regs.r12.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64))
    (h13 : u.regs.r13.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64))
    (h14 : u.regs.r14.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64))
    (h15 : u.regs.r15.toBitVec = rd t.dmem (8#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)) :
    Kg (CView P c ∗ F) s ra (fr s lo w q) u := by
  have hrd := fun i (hi : i < 7) =>
    h.kb.rd_hi (lo := lo ++ [w]) (hi := q :: saved s) rfl (i := i) (by simpa [saved] using hi)
  simp only [BitVec.add_comm (8#64) t.regs.rsp.toBitVec, BitVec.add_assoc, BitVec.reduceAdd]
    at hbx hbp h12 h13 h14 h15
  refine h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals apply UInt64.toBitVec_inj.mp
  · exact hbx.trans (hrd 1 (by decide))
  · exact hbp.trans (hrd 2 (by decide))
  · exact h12.trans (hrd 3 (by decide))
  · exact h13.trans (hrd 4 (by decide))
  · exact h14.trans (hrd 5 (by decide))
  · exact h15.trans (hrd 6 (by decide))
end

end Bbu.Unit.ClassifyU
