module

public import BbuKraken.Unit.Plan.PlannerRunDefs
import all BbuKraken.Unit.Plan.PlannerRunDefs
public import BbuKraken.Unit.Plan.Emission
import all BbuKraken.Unit.Plan.Emission
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock

@[expose] public section

/-! The frame and the return block of `Planner::run`.
The locals contain 4121 words. The six saved registers are above them, and
4113 words below the locals are available for calls. -/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def saved (s : MachineData) : List Word :=
  [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec, s.regs.r12.toBitVec,
    s.regs.r13.toBitVec, s.regs.r14.toBitVec, s.regs.r15.toBitVec]

def fr (s : MachineData) (lo locals : List Word) : List Word := lo ++ (locals ++ saved s)

structure Bd (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (lo locals : List Word) (t : MachineData) : Prop where
  kb : Kb (PlannerRunView P g ∗ F) s ra (fr s lo locals) 33016#64 t
  low : lo.length = 4113
  localLength : locals.length = 4121

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo locals : List Word}

theorem Bd.next (h : Bd P g F s ra lo locals t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) : Bd P g F s ra lo locals u :=
  ⟨h.kb.next hm hsp, h.low, h.localLength⟩

theorem Bd.length (h : Bd P g F s ra lo locals t) : (fr s lo locals).length = plannerRunD := by
  simp [fr, saved, h.low, h.localLength, plannerRunD]

theorem Bd.exit_mem (h : Bd P g F s ra lo locals t) (exitra : Int64) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true ∧
      StkMem plannerRunD (PlannerRunView P g ∗ F) s
        (t.dmem.storeInt (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt) := by
  obtain ⟨xs, w, he⟩ : ∃ xs w, lo = xs ++ [w] :=
    ⟨lo.dropLast, lo.getLast (by intro hn; have hl := h.low; rw [hn] at hl; contradiction),
      (List.dropLast_concat_getLast _).symm⟩
  have hm := h.kb.mem
  rw [fr, he, List.append_assoc, List.singleton_append] at hm
  have ha : t.regs.rsp.toBitVec - 8#64 =
      rsp s - 8#64 - BitVec.ofNat 64 (8 * ((locals ++ saved s).length + 1)) := by
    rw [h.kb.sp]
    simp only [List.length_append, h.localLength, saved, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    bv_omega
  refine ⟨Stk.wd_isSome hm ha, xs ++ exitra.toBitVec :: (locals ++ saved s),
    ra.toBitVec, ?_, Stk.wd_store hm ha exitra.toBitVec⟩
  have hl := h.length
  simpa only [fr, he, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hl

theorem Bd.popSome (h : Bd P g F s ra lo locals t) (i : Nat) (hi : i < 6) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 32968#64 + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  have ha : t.regs.rsp.toBitVec + 32968#64 + BitVec.ofNat 64 (8 * i) =
      t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (locals.length + i)) := by
    rw [h.localLength, Nat.mul_add, show 8 * 4121 = 32968 by omega, BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
  rw [ha]
  exact h.kb.isSome_hi (lo := lo) (hi := locals ++ saved s)
    (by simp [h.localLength, saved]) (by simp [h.localLength, saved]; omega)

theorem Bd.popRead (h : Bd P g F s ra lo locals t) (i : Nat) (hi : i < 6) :
    rd t.dmem (t.regs.rsp.toBitVec + 32968#64 + BitVec.ofNat 64 (8 * i)) = (saved s)[i] := by
  have ha : t.regs.rsp.toBitVec + 32968#64 + BitVec.ofNat 64 (8 * i) =
      t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (locals.length + i)) := by
    rw [h.localLength, Nat.mul_add, show 8 * 4121 = 32968 by omega, BitVec.ofNat_add]
    simp only [BitVec.add_assoc]
  rw [ha]
  have hr := h.kb.rd_hi (lo := lo) (hi := locals ++ saved s)
    (by simp [h.localLength, saved]) (i := locals.length + i)
    (by simp [h.localLength, saved]; omega)
  rw [List.getElem_append_right (by rw [h.localLength]; omega)] at hr
  simp only [Nat.add_sub_cancel_left] at hr
  exact hr

theorem Bd.pop (h : Bd P g F s ra lo locals t) (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 32968#64 + t.regs.rsp.toBitVec + 48#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (32968#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 8#64))
    (h12 : u.regs.r12.toBitVec = rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 16#64))
    (h13 : u.regs.r13.toBitVec = rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 24#64))
    (h14 : u.regs.r14.toBitVec = rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 32#64))
    (h15 : u.regs.r15.toBitVec = rd t.dmem (32968#64 + t.regs.rsp.toBitVec + 40#64)) :
    Kg (PlannerRunView P g ∗ F) s ra (fr s lo locals) u := by
  have hrd := h.popRead
  simp only [BitVec.add_comm (32968#64) t.regs.rsp.toBitVec] at hbx hbp h12 h13 h14 h15
  refine h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega) ?_ ?_ ?_ ?_ ?_ ?_
  all_goals apply UInt64.toBitVec_inj.mp
  · exact hbx.trans (by simpa [saved] using hrd 0 (by decide))
  · exact hbp.trans (by simpa [saved] using hrd 1 (by decide))
  · exact h12.trans (by simpa [saved] using hrd 2 (by decide))
  · exact h13.trans (by simpa [saved] using hrd 3 (by decide))
  · exact h14.trans (by simpa [saved] using hrd 4 (by decide))
  · exact h15.trans (by simpa [saved] using hrd 5 (by decide))

end

theorem plannerRunQ_rax {g g' : PlannerRunG} {s t u : MachineData}
    (h : plannerRunQ g g' s t) (hax : rax u = rax t) : plannerRunQ g g' s u := by
  obtain ⟨us, hcode, hrest⟩ := h
  exact ⟨us, (congrArg (fun w : Word => w.setWidth 8) hax).trans hcode, hrest⟩

end Bbu.Unit.PlannerRunU
