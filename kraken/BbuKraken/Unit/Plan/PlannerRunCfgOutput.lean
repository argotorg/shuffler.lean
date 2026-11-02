module

public import BbuKraken.Unit.Plan.PlannerRunCfgDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgDefs
public import BbuKraken.Unit.Plan.PlannerRunOutputStart
import all BbuKraken.Unit.Plan.PlannerRunOutputStart
public import BbuKraken.Unit.Plan.PlannerRunOutputCopy
import all BbuKraken.Unit.Plan.PlannerRunOutputCopy
public import BbuKraken.Unit.Plan.PlannerRunOutputCount
import all BbuKraken.Unit.Plan.PlannerRunOutputCount

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

section
variable [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)

set_option maxRecDepth 4096 in
theorem cfg_16 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.9" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, EmittedPhase] at ht
  obtain ⟨current, M, ctx, hal, hn, ht⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.9") 11 t b j u
  have hh := b_16 P current M F s t ra (I' (.label ".LB.Planner.run.10") 12)
    I' (RunExit P g F s ra) (by
      intro u hu ha hz
      obtain ⟨lo, locals, hb⟩ := hu
      have hs : ctx.status ≠ .done := status_ne_of_al_eq (ha.trans hal) hz
      have rr := ctx.terminal hn
      simp only [hs, ↓reduceIte] at rr
      apply Program.Intercept.intro_label (i := 13) (by decide)
      left
      refine ⟨hb.kb.stack (by decide), ?_, Or.inl (by simp [runV])⟩
      simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, RunReturn]
      refine ⟨current, lo, locals, hb.toBd, hb.ok, rr.finish (ha.trans hal) ?_⟩
      simpa only [hs, ↓reduceIte] using ctx.count) (by
      intro u hu hpres ha hz
      have hs : ctx.status = .done := status_eq_of_al_eq (hpres.trans hal) ha
      have hend : Flat.sourcesFrom current.p.n 0 M current.sources = current.sources :=
        sources_end (by rw [hz]; decide)
      have rr := ctx.terminal hn
      simp only [hs, ↓reduceIte, hend] at rr
      apply Program.Intercept.intro_label (i := 12) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, SourceDonePhase]
        exact ⟨current, M, ⟨rr⟩, ha, hu⟩
      · simp [runV]) (by
      intro u hu hpres ha
      have hs : ctx.status = .done := status_eq_of_al_eq (hpres.trans hal) ha
      have rr := ctx.terminal hn
      simp only [hs, ↓reduceIte] at rr
      refine ⟨?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, SourcePhase]
        exact ⟨current, M, Flat.sourcesFrom current.p.n 0 M current.sources,
          ⟨rr⟩, ctx.count, ha, hu⟩
      · have hsize := congrArg PG.n ctx.stable.planner
        change current.p.n = g.p.n at hsize
        have hbound := hu.choose_spec.choose_spec.1.ok.planner.n
        rw [hsize] at hbound
        change g.p.n.toNat ≤ 1024 at hbound
        simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_17 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.10" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, SourcePhase] at ht
  obtain ⟨current, M, wanted, ⟨rr⟩, hc, ha, ht⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.10") 12 t b j u
  have hh := b_17 P current M F s t ra wanted (I' (.label ".LB.Planner.run.11") 13)
    I' (RunExit P g F s ra) (by
      intro sources u he hu hal
      apply Program.Intercept.intro_label (i := 11) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, SourcePhase]
        exact ⟨{current with sources := sources}, M, wanted, ⟨rr⟩, hc, hal.trans ha, hu⟩
      · have hi := ht.choose_spec.choose_spec.2.2.2.1
        have hui := hu.choose_spec.choose_spec.2.2.2.1
        have hsize := congrArg PG.n rr.stable.planner
        change current.p.n = g.p.n at hsize
        change rdx t < current.p.n at hi
        change rdx u < current.p.n at hui
        rw [hsize] at hi hui
        have hs : (rdx u).toNat = (rdx t).toNat + 1 := by rw [he]; bv_omega
        simp only [runV, String.reduceEq, or_false, ↓reduceIte, hs]
        change (rdx t).toNat < g.p.n.toNat at hi
        change (rdx u).toNat < g.p.n.toNat at hui
        omega) (by
      intro sources u hu he hal
      subst sources
      refine ⟨?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, SourceDonePhase]
        exact ⟨{current with sources := wanted}, M, ⟨rr⟩, hal.trans ha, hu⟩
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_18 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.11" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, SourceDonePhase] at ht
  obtain ⟨current, M, ⟨rr⟩, ha, ht⟩ := ht
  have hok := ht.choose_spec.choose_spec.1.ok
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.11") 13 t b j u
  have hh := b_18 P current M F s t ra (I' (.label ".LB.Planner.run.12") 14)
    I' (RunExit P g F s ra) (by
      intro u lo locals hb hal
      refine ⟨?_, Or.inl (by simp [runV])⟩
      simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, RunReturn]
      refine ⟨{current with count := BitVec.ofNat 64 current.traceLength}, lo, locals, hb,
        ⟨hok.planner, hok.spillCount, hok.sourceIds, hok.targetIds, hok.ops, hok.traceLength⟩,
        (rr.withCount _).finish (hal.trans ha) ?_⟩
      change BitVec.ofNat 64 current.traceLength = BitVec.ofNat 64 current.state.trace.length
      rw [PlannerRunG.trace_length hok])
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

end
end Bbu.Unit.PlannerRunU
