import BbuKraken.Unit.Plan.PlannerRunCheckDefs

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU

set_option maxRecDepth 4096 in
theorem b_19_24 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (R : Prop) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hret : ∀ u, (∃ lo locals, Bd P g F s ra lo locals u ∧ R) → al u = 2#8 →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E
        (label ".LB.Planner.run.26") u) :
    plannerRunAsm.ForallBlocks fun blk =>
      blk.label ∈ [.label ".LB.Planner.run.19", .label ".LB.Planner.run.20",
        .label ".LB.Planner.run.21", .label ".LB.Planner.run.22",
        .label ".LB.Planner.run.23", .label ".LB.Planner.run.24"] →
      ∀ t, (∃ lo locals, Bd P g F s ra lo locals t ∧ R) → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]
  simp only [and_self]
  intro t ⟨lo, locals, hb, hr⟩
  kvcgen64
  all_goals try symexec_norm at ⊢
  apply hret _ ?_ rfl
  exact ⟨lo, locals, hb.next rfl rfl, hr⟩

end Bbu.Unit.PlannerRunU
