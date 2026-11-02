module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionDefs
import all FlatShuffler.Unit.Plan.PlannerRunEmissionDefs
public import FlatShuffler.Unit.Run.Model
import all FlatShuffler.Unit.Run.Model

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open Flat

set_option maxRecDepth 4096 in
theorem b_14 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64) (hok : g.Ok)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hdone : ∀ u, EmitReady P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.15") u)
    (hnext : ∀ u, rax u = 8#64 + rax t → EmitCountHead P g M F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.7" →
      EmitCountNext P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, j, c, hc, hj, hax, hdx, hp, hmodel⟩
  have hn := hok.planner.targetSizeFitsBuffer
  have hjN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) hn
  have hptr (b : Bool) (he : (rdx t - (8#64 + rax t) == 0#64) = b) :
      ((j + 1#64 == g.p.targetSize) = b) := by
    rw [hax, hdx] at he
    have heq : (t.regs.rsp.toBitVec + 16480#64 + g.p.targetSize * 8#64 -
        (8#64 + (t.regs.rsp.toBitVec + 16480#64 + j * 8#64)) == 0#64) =
        (j + 1#64 == g.p.targetSize) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq]
      change g.p.targetSize.toNat ≤ 1024 at hn
      bv_omega
    exact heq.symm.trans he
  have hax' : t.regs.rax.toBitVec = t.regs.rsp.toBitVec + 16480#64 + j * 8#64 := hax
  have hdx' : t.regs.rdx.toBitVec = t.regs.rsp.toBitVec + 16480#64 + g.p.targetSize * 8#64 := hdx
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.run.15" =>
    rename_i he
    symexec_norm at he
    have hjend : j + 1#64 = g.p.targetSize := beq_iff_eq.mp (hptr true he)
    apply hdone
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
    change Flat.unmappedFrom (countState g M) (j + 1#64) c = _ at hmodel
    rw [hjend] at hmodel
    have hend : Flat.unmappedFrom (countState g M) g.p.targetSize c = c := RunU.unmapped_end
    rw [hend] at hmodel
    exact hp.trans (congrArg some hmodel)
  | other =>
    rename_i he
    symexec_norm at he
    have hjnext : j + 1#64 < g.p.targetSize := by
      have hne := beq_eq_false_iff_ne.mp (hptr false he)
      bv_omega
    apply hnext
    · rfl
    refine ⟨lo, locals, j + 1#64, c, hc.next rfl rfl rfl rfl rfl rfl rfl rfl,
      hjnext, ?_, hdx, hp, hmodel⟩
    simp only [rax, Reg64s.get64_rax, hax']
    bv_omega

end FlatShuffler.Unit.PlannerRunU
