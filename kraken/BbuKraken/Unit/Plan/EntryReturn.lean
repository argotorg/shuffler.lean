module

public import BbuKraken.Unit.Plan.EntryFrame
import all BbuKraken.Unit.Plan.EntryFrame

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

section
variable {g : EG} {F : MProp 64} {s t u : MachineData} {ra : Int64}
    {lo locals : List Word}

theorem Bd.length (h : Bd g F s ra lo locals t) : (fr s lo locals).length = entryD := by
  simp [fr, h.low, h.localLength, entryD]

theorem Bd.savedFocus (h : Bd g F s ra lo locals t) :
    ∃ R, Stk (rsp s) (fr s lo locals) ra.toBitVec ∗ (View (rsp s) g ∗ F) =
      Wd (t.regs.rsp.toBitVec + 80#64) s.regs.rbx.toBitVec ∗ R := by
  have ha : rsp s - 8#64 - 66016#64 + 65928#64 + 80#64 =
      t.regs.rsp.toBitVec + 80#64 := by rw [h.kb.sp]; bv_omega
  refine ⟨Arr (rsp s - 8#64 - 66016#64) lo ∗
    Arr (rsp s - 8#64 - 66016#64 + 65928#64) locals ∗
    Wd (rsp s - 8#64) ra.toBitVec ∗ (View (rsp s) g ∗ F), ?_⟩
  simp only [Stk, fr, List.length_append, h.low, h.localLength, List.length_singleton,
    Nat.reduceAdd, Nat.reduceMul, Arr.append, Arr, MProp.sep_emp, ha]
  ecancel

theorem Bd.popSome (h : Bd g F s ra lo locals t) :
    (t.dmem.loadInt (80#64 + t.regs.rsp.toBitVec) 8).isSome = true := by
  obtain ⟨R, he⟩ := h.savedFocus
  rw [BitVec.add_comm (80#64)]
  exact Wd.isSome (he ▸ h.kb.mem)

theorem Bd.pop (h : Bd g F s ra lo locals t)
    (hm : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = 80#64 + t.regs.rsp.toBitVec + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem (80#64 + t.regs.rsp.toBitVec))
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h14 : u.regs.r14 = t.regs.r14)
    (h15 : u.regs.r15 = t.regs.r15) :
    Kg (View (rsp s) g ∗ F) s ra (fr s lo locals) u := by
  obtain ⟨R, he⟩ := h.savedFocus
  have hr : rd t.dmem (t.regs.rsp.toBitVec + 80#64) = s.regs.rbx.toBitVec :=
    rd_of_eq (he ▸ h.kb.mem) (by rfl)
  refine h.kb.kg hm (by rw [hsp, h.kb.sp]; bv_omega) ?_
    (hbp.trans h.bp) (h12.trans h.r12) (h13.trans h.r13)
    (h14.trans h.r14) (h15.trans h.r15)
  apply UInt64.toBitVec_inj.mp
  rw [hbx, BitVec.add_comm (80#64)]
  exact hr

end

set_option maxRecDepth 4096 in
theorem b_9 [Host] [FunDecls] (g : EG) (F : MProp 64) (s t : MachineData)
    (ra : Int64) (Q : MachineData → Prop)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (hq : ∀ lo locals u, Bd g F s ra lo locals t →
      StkMem entryD (View (rsp s) g ∗ F) s u.dmem → rax u = rdx t → Q u) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.9" →
      (∃ lo locals, Bd g F s ra lo locals t) → WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I'
          (fun a u => a = ra ∧ Q u ∧ Sep.mod.Agree s u)) t := by
  cfg_block
  intro ⟨lo, locals, hb⟩
  have kp := hb.popSome
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => with_reducible exact kp
  | retAddr =>
    refine Option.isSome_iff_exists.mpr ⟨ra, Kg.retAddr
      (P := View (rsp s) g ∗ F) (s := s) (fr := fr s lo locals) ?_⟩
    exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.ret (post := fun _ u => Q u) (P := View (rsp s) g ∗ F) (fr := fr s lo locals) ?_
      fun u hmem hax => ?_
    · exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
    · apply hq lo locals u hb
      · exact ⟨fr s lo locals, ra.toBitVec, hb.length, hmem ▸ hb.kb.mem⟩
      · exact hax

end Bbu.Unit.EntryValidU
