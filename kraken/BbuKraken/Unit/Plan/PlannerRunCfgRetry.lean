module

public import BbuKraken.Unit.Plan.PlannerRunCfgDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgDefs
public import BbuKraken.Unit.Plan.PlannerRunRetryAfter
import all BbuKraken.Unit.Plan.PlannerRunRetryAfter
public import BbuKraken.Unit.Plan.PlannerRunFailure
import all BbuKraken.Unit.Plan.PlannerRunFailure

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

section
variable [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)

set_option maxRecDepth 4096 in
theorem cfg_31 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.18" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, before, ctx, hres, ht⟩ := ht
  obtain ⟨lo, locals, i, h0, hi, ha, hc, hbp, hmodel⟩ := ht
  have ht : DropAfterHead P current M F s ra before t :=
    ⟨lo, locals, i, h0, hi, ha, hc, hbp, hmodel⟩
  have hsize := congrArg PG.m ctx.stable.planner
  change current.p.m = g.p.m at hsize
  have hdrp := congrArg PG.drp ctx.stable.planner
  change current.p.drp = g.p.drp at hdrp
  have hiN : i.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h0.ok.planner.m
  have hix : (rax t - g.p.drp).toNat = i.toNat := by rw [ha, hdrp]; bv_omega
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.18") 20 t b j u
  have hh := b_31 P current M F s t ra before (I' (.label ".LB.Planner.run.19") 21)
    I' (RunExit P g F s ra) (by
      intro u hau hu
      obtain ⟨lo', locals', j, h1, hj, haj, hcj, hbpj, hmodelj⟩ := hu
      have hu : DropAfterHead P current M F s ra before u :=
        ⟨lo', locals', j, h1, hj, haj, hcj, hbpj, hmodelj⟩
      have hjN : j.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) h1.ok.planner.m
      have hjx : (rax u - g.p.drp).toNat = j.toNat := by rw [haj, hdrp]; bv_omega
      have hij : j.toNat = i.toNat + 1 := by
        rw [haj, ha] at hau
        bv_omega
      apply Program.Intercept.intro_label (i := 19) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show RetryPhase P g F s ra u from ⟨current, M, before, ctx, hres, hu⟩)
      · have hin := BitVec.lt_def.mp hi
        have hjn := BitVec.lt_def.mp hj
        rw [hsize] at hin hjn
        simp only [runV, String.reduceEq, or_false, ↓reduceIte, hbp, hbpj, hix, hjx]
        omega) (by
      intro u hp hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := dropBudget_eq ctx.stable h1.kb.vmem
      have hdec : (current.p.m - Flat.droppedCount current.p.m current.dropped).toNat <
          (current.p.m - before).toNat :=
        Flat.sub_lt_sub (Flat.droppedCount_le _ _) (by
          have hle := Flat.droppedCount_le current.p.m current.dropped
          have hlt := BitVec.lt_def.mp hp
          omega) hp
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => PrepareHead P a F s ra) u from
            ⟨current, h0.ok, ⟨ctx.retry hres hp⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hbp, hix, hb]
        rw [← hsize]
        omega) (by
      intro u hp hu
      obtain ⟨lo', locals', h1⟩ := hu
      apply Program.Intercept.intro_label (i := 14) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show RetryFailPhase P g F s ra u from
            ⟨current, before, lo', locals', ctx, hres, hp, h1, h0.ok⟩)
      · simp only [runV, String.reduceEq, or_false, or_true, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_24
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit") :
    plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.13" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, before, lo, locals, ctx, hres, hp, h0, hok⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.13") 15 t b j u
  have hh := assertion_block P current F s ra (I' (.label ".LB.Planner.run.14") 16)
    I' (RunExit P g F s ra) hexit hout (by
      intro u hm ha
      exact Or.inr ⟨rfl, ha, current, (ctx.noProgress hres hp).exit ctx.count, hok, hm⟩)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, List.mem_cons, List.not_mem_nil,
    CfgLabel.label.injEq, reduceCtorEq, String.reduceEq, or_false, or_true,
    false_implies, true_implies, and_true, true_and, and_self] at hh
  exact hh t ⟨lo, locals, h0⟩

end
end Bbu.Unit.PlannerRunU
