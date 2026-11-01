module

public import BbuKraken.Unit.Plan.PlannerRunEmissionCountSetup
import all BbuKraken.Unit.Plan.PlannerRunEmissionCountSetup

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Flat Bbu.Sep

set_option maxRecDepth 4096 in
theorem b_27 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (M : Flat.Mapping)
    (F : MProp 64) (s : MachineData) (ra : Int64) (hok : g.Ok) (hn : g.p.n = 0#64)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hdone : ∀ u, EmitReady P g M F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.27" →
      ∀ t, EmitMapped P g M F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hc, hd, hp⟩
  let sp := t.regs.rsp.toBitVec
  let v : MachineData := { t with
    dmem := (t.dmem.storeInt (sp + 32920#64) 8 0).storeInt
      (sp + 32944#64) 8 (sp + 96#64).toInt }
  have hv : EmitCountLI P g M F s ra lo (setupLocals locals sp) v :=
    hc.setupCount hok hd hp rfl rfl rfl rfl rfl rfl rfl rfl
  have k0 := hc.localSome (i := 4115) (by decide)
  have k1 := (hc.storeLocal hok (i := 4115) (by decide) (by decide) 0#64
    (u := {t with dmem := t.dmem.storeInt (sp + 32920#64) 8 0})
    rfl rfl rfl rfl rfl rfl rfl rfl).localSome (i := 4118) (by decide)
  simp only [sp] at k0 k1
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => simp only [k0, k1]
  | other =>
    apply hdone
    refine ⟨lo, setupLocals locals sp, hv.next rfl rfl rfl rfl rfl rfl rfl rfl, ?_⟩
    have hend : Flat.unmappedFrom (countState g M) 0 0 = 0 := by
      have hz : ¬ (0 : Word) < (countState g M).targetSize := by
        change ¬ (0 : Word) < g.p.n
        rw [hn]
        decide
      rw [Flat.unmappedFrom, dite_eq_right hz]
    rw [hend]
    exact setupLocals.pending hc.localLength sp

end Bbu.Unit.PlannerRunU
