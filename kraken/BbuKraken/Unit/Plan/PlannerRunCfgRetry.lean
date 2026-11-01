module

public import BbuKraken.Unit.Plan.PlannerRunCfgDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgDefs
public import BbuKraken.Unit.Plan.PlannerRunRetryAfter
import all BbuKraken.Unit.Plan.PlannerRunRetryAfter
public import BbuKraken.Unit.Plan.PlannerRunBuilderFailure
import all BbuKraken.Unit.Plan.PlannerRunBuilderFailure

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
    blk.label = .label ".LB.Planner.run.31" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] at ht
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
      Program.Decreases (runV g) (.label ".LB.Planner.run.31") 33 t b j u
  have hh := b_31 P current M F s t ra before (I' (.label ".LB.Planner.run.32") 34)
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
      apply Program.Intercept.intro_label (i := 32) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
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
      apply Program.Intercept.intro_label (i := 6) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show LoopPhase g s (fun a => PrepareHead P a F s ra) u from
            ⟨current, h0.ok, ⟨ctx.retry hres hp⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hbp, hix, hb]
        rw [← hsize]
        omega) (by
      intro u hp hu hal
      obtain ⟨lo', locals', h1⟩ := hu
      have hq := (ctx.noProgress hres hp).finish hal ctx.count
      apply Program.Intercept.intro_label (i := 27) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show RunReturn P g F s ra u from ⟨current, lo', locals', h1, h0.ok, hq⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
private theorem build_failure_obl (lab : Label) (blk : Program.Block)
    (hl : lab ∈ [".LB.Planner.run.19", ".LB.Planner.run.20", ".LB.Planner.run.21",
      ".LB.Planner.run.22", ".LB.Planner.run.23"])
    (hlabel : blk.label = .label lab)
    (hblock : plannerRunAsm.blockAt lab = some blk) :
    RunObl P g F s ra resolvePhase blk := by
  intro t ht
  rw [hlabel] at ht
  have hphase : BuildFailPhase P g F s ra t := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true,
        ↓reduceIte] using ht
  obtain ⟨current, M0, hok, ⟨ctx⟩, lo, locals, h0, hi, hb⟩ := hphase
  have hsrc : runV g lab t = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      simp only [runV, String.reduceEq, or_false, or_true, ↓reduceIte]
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) blk.label blk.idx t b j u
  let R := M0.init current.p.m current.p.n = M0 ∧
    Flat.buildMapping (plannerBuilder current s M0 0#8).fl M0 = none
  have hh := b_19_24 P current F s ra R (I' blk.next (blk.idx + 1))
    I' (RunExit P g F s ra) (by
      intro u hu hal
      obtain ⟨lo', locals', h1, hi', hb'⟩ := hu
      have hq := ctx.mapping_fail hok M0 hi' hb' hal
      apply Program.Intercept.intro_label (i := 27) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show RunReturn P g F s ra u from ⟨current, lo', locals', h1, hok, hq⟩)
      · change Program.Decreases (runV g) blk.label blk.idx t
          (.label ".LB.Planner.run.26") 28 u
        rw [hlabel]
        left
        rw [hsrc]
        simp only [runV, ↓reduceIte]
        decide)
  have hh' := hh.blockAt hblock
  have hmem : blk.label ∈ [.label ".LB.Planner.run.19", .label ".LB.Planner.run.20",
      .label ".LB.Planner.run.21", .label ".LB.Planner.run.22",
      .label ".LB.Planner.run.23", .label ".LB.Planner.run.24"] := by
    rw [hlabel]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> simp
  exact hh' hmem t ⟨lo, locals, h0.toBd, hi, hb⟩

set_option maxRecDepth 4096 in
theorem cfg_19_23 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label ∈ [.label ".LB.Planner.run.19", .label ".LB.Planner.run.20",
      .label ".LB.Planner.run.21", .label ".LB.Planner.run.22",
      .label ".LB.Planner.run.23"] → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]
  repeat' apply And.intro
  all_goals
    apply build_failure_obl P g F s ra resolvePhase _ _ (by simp) rfl
    simp only [Program.blockAt, hv, Program.blockAtAux, String.reduceEq,
      ↓reduceIte, Nat.reduceAdd, Program.firstLabel]

set_option maxRecDepth 4096 in
theorem cfg_24 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.24" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] at ht
  obtain ⟨current, before, lo, locals, ctx, hres, hp, h0, hok⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.24") 26 t b j u
  let R := ¬ Flat.droppedCount current.p.m current.dropped > before
  have hh := b_19_24 P current F s ra R (I' (.label ".LB.Planner.run.25") 27)
    I' (RunExit P g F s ra) (by
      intro u hu hal
      obtain ⟨lo', locals', h1, hp'⟩ := hu
      have hq := (ctx.noProgress hres hp').finish hal ctx.count
      apply Program.Intercept.intro_label (i := 27) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show RunReturn P g F s ra u from ⟨current, lo', locals', h1, hok, hq⟩)
      · simp only [runV, String.reduceEq, or_false, or_true, ↓reduceIte]
        decide)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, List.mem_cons, List.not_mem_nil, CfgLabel.label.injEq,
    reduceCtorEq, String.reduceEq, or_false, or_true, false_implies,
    true_implies, and_true, true_and] at hh
  exact hh.2.2.2.2.2 t ⟨lo, locals, h0, hp⟩

end
end Bbu.Unit.PlannerRunU
