import BbuKraken.Unit.Plan.ClassifyFreeModel
import ProofKit.Lea32
open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true
namespace Bbu.Unit.ClassifyU
open Bbu.Sep
variable [Host] [FunDecls] (P : Addr) (c : CG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_1 : classifyAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.classify.1" → Obl P c F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body] at ht
  obtain ⟨lo, w, q, hli, hr⟩ := ht
  obtain ⟨R, hm⟩ := hli.toBd.localWord
  have k_op := Wd.isSome_byte hm (j := 3) (by decide)
  have h_op := Wd.rdb_byte hm (j := 3) (by decide)
  have hk := hli.r13
  have hstack : ¬ 0 < (t.regs.rsp.toBitVec - (s.pushRa ra).regs.rsp.toBitVec).toInt :=
    hli.kb.stack (by decide)
  unfold rdb at h_op
  clear hm
  kvcgen64 [lea32_neg1_spec]
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => exact k_op
  | goto ".LB.Planner.classify.7" =>
    have hf : (inp c s).free = true := by
      first
      | (rename_i hj hop
         run_tac Lean.Elab.Tactic.withMainContext do
           let d ← Lean.Meta.getLocalDeclFromUserName `hj
           let ty ← Lean.instantiateMVars d.type
           unless ty.isAppOfArity ``Eq 3 && ty.appArg!.isConstOf ``Bool.false do
             throwError "not the opcode branch"
         rw [MachineData.status_mk, Idioms.cmp_be_imm (w := 8) _ 1 (by decide)] at hj
         symexec_norm at hj hop
         replace hj := (kind_flag_sub t.regs.r13.toBitVec (inp c s).slot.kind hk).symm.trans hj
         have hn : (inp c s).slot.kind ≠ Junk := by
           simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hj
           exact hj.1
         have he : (inp c s).slot.valueOpcode = Const := by
           have hv := op_flag (rdb t.dmem (t.regs.rsp.toBitVec + 3#64))
             (inp c s).slot.valueOpcode (h_op.trans (hli.locals hn).2)
           exact beq_iff_eq.mp (hv.symm.trans hop)
         exact free_of_op (inp c s) he)
      | (rename_i hj
         rw [MachineData.status_mk, Idioms.cmp_be_imm (w := 8) _ 1 (by decide)] at hj
         symexec_norm at hj
         replace hj := (kind_flag_sub t.regs.r13.toBitVec (inp c s).slot.kind hk).symm.trans hj
         exact free_of_range (inp c s) hj)
    cfg_goto
    · change ¬ 0 < (t.regs.rsp.toBitVec - (s.pushRa ra).regs.rsp.toBitVec).toInt
      exact hstack
    · simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Result]
      exact ⟨lo, w, q, hli.toBd.next rfl rfl, (hr.trans (rank_free (inp c s) hf)).symm⟩
    · left; simp [V, Names.classify]
  | other =>
    rename_i hj hop
    rw [MachineData.status_mk, Idioms.cmp_be_imm (w := 8) _ 1 (by decide)] at hj
    symexec_norm at hj hop
    replace hj := (kind_flag_sub t.regs.r13.toBitVec (inp c s).slot.kind hk).symm.trans hj
    have hn : (inp c s).slot.kind ≠ Junk := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hj
      exact hj.1
    have he : (inp c s).slot.valueOpcode ≠ Const := by
      have hv := op_flag (rdb t.dmem (t.regs.rsp.toBitVec + 3#64))
        (inp c s).slot.valueOpcode (h_op.trans (hli.locals hn).2)
      exact beq_eq_false_iff_ne.mp (hv.symm.trans hop)
    have hf : (inp c s).free = false := free_false (inp c s) hj he
    first
    | (run_tac Lean.Elab.Tactic.withMainContext do
         let ty := (← Lean.Elab.Tactic.getMainTarget).consumeMData
         unless ty.isAppOf ``Inv || ty.isAppOf ``Body || ty.isAppOf ``Exists do
           throwError "not an invariant goal"
       simp only [Inv, Names.classify, String.reduceEq, ↓reduceIte, Body]
       refine ⟨lo, w, q, ?_, hr, hf⟩
       apply LI.next hli <;> rfl)
    | (left; change (8 : Nat) < 9; decide)

end Bbu.Unit.ClassifyU
