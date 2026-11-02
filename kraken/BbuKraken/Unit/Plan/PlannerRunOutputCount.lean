module

public import BbuKraken.Unit.Plan.PlannerRunOutputDefs
import all BbuKraken.Unit.Plan.PlannerRunOutputDefs
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

set_option maxRecDepth 4096 in
theorem b_18 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s t : MachineData) (ra : Int64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hret : ∀ u lo locals,
      Bd P {g with count := BitVec.ofNat 64 g.traceLength} F s ra lo locals u →
      al u = al t → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.11" →
      SourcesDone P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro ⟨lo, locals, hc, hbp⟩
  have hr := hc.localRead (i := 2066) (by decide)
  have he := hc.nops
  rw [List.getElem?_eq_getElem (by rw [hc.localLength]; decide)] at he
  replace hr := hr.trans (Option.some.inj he)
  have kn := hc.localSome (i := 2066) (by decide)
  have kc : (t.dmem.loadInt g.countPtr 8).isSome = true :=
    isSome_of_eq g.count hc.kb.vmem (by unfold PlannerRunView; ecancel)
  simp only [Nat.reduceMul] at hr kn
  unfold rd at hr
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hbp, hr] at ⊢
  vc_by_shape
  | load => run_loads [kn, kc]
  | other =>
    apply hret _ lo locals
    · exact hc.storeCount _ rfl rfl
    · rfl

end Bbu.Unit.PlannerRunU
