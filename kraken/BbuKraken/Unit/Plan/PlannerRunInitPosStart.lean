import BbuKraken.Unit.Plan.PlannerRunInitDefs

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU

private theorem zero_lt {w : Word} (h : w ≠ 0#64) : 0#64 < w := by bv_omega

set_option maxRecDepth 4096 in
theorem b_7 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hempty : ∀ u, InitDone P g F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.9") u)
    (hinit : ∀ u, rax u = u.regs.rsp.toBitVec + 96#64 →
      InitPosHead P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.7" →
      ∀ t, InitDestDone P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, hp⟩
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | goto ".LB.Planner.run.9" =>
    rename_i af hz
    symexec_norm at hz
    simp only [hc.rsi, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hempty
    refine ⟨lo, locals, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hp, ?_⟩
    rw [hz]
    exact InitPrefix.zero _ _
  | other =>
    rename_i af hz
    symexec_norm at hz
    simp only [hc.rsi, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hinit
    · rfl
    refine ⟨lo, locals, 0#64, hc.next rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      zero_lt hz, ?_, ?_, hp, InitPrefix.zero _ _⟩
    · simp only [rax, Reg64s.get64_rax, BitVec.zero_mul, BitVec.add_zero]
    · simp only [rcx, Reg64s.get64_rcx, hc.rsi]

end Bbu.Unit.PlannerRunU
