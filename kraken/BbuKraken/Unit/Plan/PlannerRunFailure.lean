module

public import BbuKraken.Unit.Plan.PlannerRunValidate
import all BbuKraken.Unit.Plan.PlannerRunValidate

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

set_option maxRecDepth 4096 in
theorem assertion_block [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit")
    (hX : ∀ u, StkMem plannerRunD (PlannerRunView P g ∗ F) s u.dmem →
      u.regs.get64 .rdi = 1#64 → E (label "exit") u) :
    plannerRunAsm.ForallBlocks fun blk =>
      blk.label ∈ [.label ".LB.Planner.run.4", .label ".LB.Planner.run.13"] →
      ∀ t, (∃ lo locals, Bd P g F s ra lo locals t) → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]
  try simp only [and_self]
  intro t ⟨lo, locals, hb⟩
  have he := ProofKit.external_call_spec "exit" hexit
  kvcgen64 [he]
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => exact (hb.exit_mem 0).1
  | jumpOut =>
    refine Or.inr ⟨hX _ (hb.exit_mem _).2 rfl, ?_⟩
    intro l hl heq
    exact False.elim (hout l hl heq)

end Bbu.Unit.PlannerRunU
