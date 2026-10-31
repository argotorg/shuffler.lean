import BbuKraken.Unit.Plan.ResolveInitDefs

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

section
variable [Host] [FunDecls]
  (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)

theorem b_4 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.4" →
      Obl P r F s ra (initFullPhase P r F s ra rest) (initFullVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
    String.reduceEq, ↓reduceIte, Scan, Bool.true_eq] at ht
  obtain ⟨lo, L, u0, count, hc, hbp, hp, hcount, hnext, he⟩ := ht
  have h9 : t.regs.r9.toBitVec = r9 s := hc.r9
  symexec_norm at h9 hp hcount hnext he
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.resolve.7" =>
    rename_i hj
    symexec_norm at hj
    have hend : ¬ (rdx t + 1#64) < r9 s := by
      change ¬ (t.regs.rdx.toBitVec + 1#64) < s.regs.r9.toBitVec
      have hh := hj
      idioms at hh
      rw [h9] at hh
      bv_omega
    cfg_goto
    · exact hc.bd.kb.stack (by decide)
    · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
        String.reduceEq, ↓reduceIte, CandidatesDone]
      refine ⟨lo, L, u0, count, hc.next rfl rfl rfl rfl rfl rfl, hbp, ?_⟩
      exact he.trans (candidates_done hend)
    · left
      simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
      omega
  | other =>
    first
    | (simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
         String.reduceEq, ↓reduceIte, Scan]
       simp only [Bool.false_eq_true, ↓reduceIte]
       symexec_norm at ⊢
       refine ⟨lo, L, u0, count, hc.next rfl rfl rfl rfl rfl rfl, hbp, ?_, ?_, ?_, ?_⟩
       · rename_i hj
         symexec_norm at hj
         have hh := hj
         idioms at hh
         rw [h9] at hh
         change 1#64 + t.regs.rdx.toBitVec < s.regs.r9.toBitVec
         bv_omega
       · simpa only [BitVec.add_comm (1#64)] using hcount
       · simpa only [BitVec.add_comm (1#64)] using hnext
       · simpa only [BitVec.add_comm (1#64)] using he)
    | (left
       simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
       symexec_norm at ⊢
       have hd := Flat.sub_succ_lt hp
       change (s.regs.r9.toBitVec - (t.regs.rdx.toBitVec + 1#64)).toNat <
         (s.regs.r9.toBitVec - t.regs.rdx.toBitVec).toNat at hd
       have heq : s.regs.r9.toBitVec - (1#64 + t.regs.rdx.toBitVec) =
           s.regs.r9.toBitVec - (t.regs.rdx.toBitVec + 1#64) := by bv_omega
       rw [heq]
       omega)

theorem b_6 : resolveAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.resolve.6" →
      Obl P r F s ra (initFullPhase P r F s ra rest) (initFullVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
    String.reduceEq, ↓reduceIte, CandidatesDone] at ht
  obtain ⟨lo, L, u0, count, hc, rfl, he⟩ := ht
  kvcgen64
  all_goals try symexec_norm at ⊢
  · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
      String.reduceEq, ↓reduceIte, CandidatesDone]
    exact ⟨lo, L, u0, 0#64, hc.next rfl rfl rfl rfl rfl rfl, rfl, he⟩
  · left
    simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
    decide

end
end Bbu.Unit.ResolveU
