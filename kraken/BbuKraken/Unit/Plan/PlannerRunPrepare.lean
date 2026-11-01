module

public import BbuKraken.Unit.Plan.PlannerRunCheckDefs
import all BbuKraken.Unit.Plan.PlannerRunCheckDefs
public import BbuKraken.Unit.Plan.PlannerRunStore
import all BbuKraken.Unit.Plan.PlannerRunStore

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU

def PrepareHead (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, LoopLI P g F s ra lo locals t ∧
    t.regs.r13.toBitVec = t.regs.rsp.toBitVec + 32#64 ∧
    locals[3]? = some g.countPtr ∧ Flat.targetsFrom g.p.fl g.spills 0 = true

set_option maxRecDepth 4096 in
theorem b_4 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hprepare : ∀ t, PrepareHead P g F s ra t → K () t) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.4" →
      ∀ t, CheckDone P g F s ra t → WP.wp blk.body K
        (Program.Intercept (Program.labels plannerRunAsm) (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, htgt⟩
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => exact hc.localSome (i := 3) (by decide)
  | other =>
    apply hprepare
    refine ⟨lo, locals.set 3 g.countPtr, ?_, rfl, ?_, htgt⟩
    · refine ⟨hc.toBd.storeLocal (i := 3) (by decide) g.countPtr ?_ rfl,
        hc.rbx, hc.r12, hc.r15, hc.r14, ?_⟩
      · simp only [Nat.reduceMul, hc.rbp]
      · simpa [List.getElem?_set] using hc.sources
    · exact List.getElem?_set_self (by rw [hc.localLength]; decide)

end Bbu.Unit.PlannerRunU
