module

public import BbuKraken.Unit.Plan.PlannerRunEmissionDefs
import all BbuKraken.Unit.Plan.PlannerRunEmissionDefs

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Flat

set_option maxRecDepth 4096 in
theorem b_12 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hzero : ∀ u, g.p.n = 0#64 → EmitMapped P g M F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.26") u)
    (hcopy : ∀ u, EmitPosHead P g M F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.13" →
      ∀ t, EmitDestDone P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, hcx, hd⟩
  have hcx' : t.regs.rcx.toBitVec = g.p.n := hcx
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.run.26" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hcx', BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hzero _ hz
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl, hd, ?_⟩
    rw [hz]
    exact WordPrefix.zero _ _ _
  | other =>
    rename_i af hz
    symexec_norm at hz
    simp only [hcx', BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hcopy
    refine ⟨lo, locals, 0#64, hc.next rfl rfl rfl rfl rfl rfl rfl rfl,
      ?_, rfl, ?_, rfl, rfl, hd, WordPrefix.zero _ _ _⟩
    · bv_omega
    · simp only [rdx, Reg64s.get64_rdx, hcx']

end Bbu.Unit.PlannerRunU
