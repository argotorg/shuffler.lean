module

public import BbuKraken.Unit.Plan.PlannerRunValidate
import all BbuKraken.Unit.Plan.PlannerRunValidate

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU

set_option maxRecDepth 4096 in
theorem b_25 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hret : ∀ u, CheckBad P g F s ra u → al u = 2#8 → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.25" →
      ∀ t, CheckBad P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hb, hbad⟩
  kvcgen64
  apply hret _ ?_ rfl
  exact ⟨lo, locals, hb.next rfl rfl rfl rfl rfl rfl rfl, hbad⟩

end Bbu.Unit.PlannerRunU
