module

public import BbuKraken.Unit.Plan.PlannerRunCfgDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgDefs
public import BbuKraken.Unit.Plan.PlannerRunPrologue
import all BbuKraken.Unit.Plan.PlannerRunPrologue
public import BbuKraken.Unit.Plan.PlannerRunCheck
import all BbuKraken.Unit.Plan.PlannerRunCheck
public import BbuKraken.Unit.Plan.PlannerRunTarget
import all BbuKraken.Unit.Plan.PlannerRunTarget
public import BbuKraken.Unit.Plan.PlannerRunScan
import all BbuKraken.Unit.Plan.PlannerRunScan
public import BbuKraken.Unit.Plan.PlannerRunSpilled
import all BbuKraken.Unit.Plan.PlannerRunSpilled
public import BbuKraken.Unit.Plan.PlannerRunFailure
import all BbuKraken.Unit.Plan.PlannerRunFailure
public import BbuKraken.Unit.Plan.PlannerRunReturn
import all BbuKraken.Unit.Plan.PlannerRunReturn

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

section
variable [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)

set_option maxRecDepth 4096 in
theorem cfg_0 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.0" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.0") 2 t b j u
  have hh := b_0 P (withSaw g 0#8) F s t ra (I' (.label ".LB.Planner.run.1") 3)
    I' (RunExit P g F s ra) (by
      intro u he hu
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · have hi := ht.choose_spec.choose_spec.2.1
        have huI := hu.choose_spec.choose_spec.2.1
        have hs : (rcx u).toNat = (rcx t).toNat + 1 := by
          rw [he]
          change rcx t < g.p.n at hi
          bv_omega
        simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        rw [hs]
        change (rcx t).toNat < g.p.n.toNat at hi
        change (rcx u).toNat < g.p.n.toNat at huI
        have hr : g.p.n.toNat - (rcx t).toNat =
            g.p.n.toNat - ((rcx t).toNat + 1) + 1 := by omega
        rw [hr]
        simp only [Nat.add_mul, Nat.one_mul]
        omega) (by
      intro u he hu
      apply Program.Intercept.intro_label (i := 5)
      · decide
      left
      refine ⟨?_, ?_, Or.inl ?_⟩
      · exact (hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide))
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · have hi := ht.choose_spec.choose_spec.2.1
        simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        change (rcx t).toNat < g.p.n.toNat at hi
        have hp : 0 < (g.p.n.toNat - (rcx t).toNat) * (g.p.m.toNat + 4) :=
          Nat.mul_pos (by omega) (by omega)
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_3 (hok : g.Ok) : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.3" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.3") 5 t b j u
  have hh := b_3 P (withSaw g 0#8) F s t ra (withSaw_ok hok _)
    (I' (.label ".LB.Planner.run.4") 6) I' (RunExit P g F s ra) (by
      intro u he hu
      apply Program.Intercept.intro_label (i := 1) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, he]
        omega) (by
      intro u he hu
      apply Program.Intercept.intro_label (i := 26) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, or_true, ↓reduceIte]
        omega) (by
      intro u he hu ha
      obtain ⟨lo, locals, hb, htgt⟩ := hu
      apply Program.Intercept.intro_label (i := 27) (by decide)
      left
      refine ⟨hb.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte, RunReturn]
        exact ⟨withSaw g 0#8, lo, locals, hb.toBd, withSaw_ok hok _,
          plannerRunQ_bad_target g s u htgt ha⟩
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_4 (hok : g.Ok) : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.4" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.4") 6 t b j u
  have hh := b_4 P (withSaw g 0#8) F s ra (I' (.label ".LB.Planner.run.5") 7)
    I' (RunExit P g F s ra) (by
      intro u hu
      let ctx := LoopContext.start g s hu.choose_spec.choose_spec.2.2.2
      refine ⟨?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte, LoopPhase]
        exact ⟨withSaw g 0#8, withSaw_ok hok _, ⟨ctx⟩, hu⟩
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        rw [dropBudget_eq ctx.stable hu.choose_spec.choose_spec.1.kb.vmem]
        have hd := Flat.droppedCount_le g.p.m g.dropped
        have hb : (g.p.m - Flat.droppedCount g.p.m g.dropped).toNat ≤ g.p.m.toNat := by
          bv_omega
        change (g.p.m - Flat.droppedCount g.p.m g.dropped).toNat * 65536 + 60000 < _
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 4096 in
theorem cfg_25 (hok : g.Ok) : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.25" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.25") 27 t b j u
  have hh := b_25 P (withSaw g 0#8) F s ra (I' (.label ".LB.Planner.run.26") 28)
    I' (RunExit P g F s ra) (by
      intro u hu ha
      obtain ⟨lo, locals, hb, htgt⟩ := hu
      refine ⟨?_, Or.inl (by simp [runV])⟩
      simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte, RunReturn]
      exact ⟨withSaw g 0#8, lo, locals, hb.toBd, withSaw_ok hok _,
        plannerRunQ_bad_target g s u htgt ha⟩)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 4096 in
theorem cfg_26 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.26" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte, RunReturn] at ht
  obtain ⟨current, lo, locals, hb, hok, hq⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.26") 28 t b j u
  have hh := b_26 P g current F s ra hok (I' (.label ".LB.Planner.run.27") 29) I'
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ⟨lo, locals, hb, hq⟩

theorem cfg_entry : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .entry → RunObl P g F s ra resolvePhase blk := by
  cfg_block [RunObl]
  intro t ht
  kvcgen64
  simpa only [RunInv, Names.plannerRun, ↓reduceIte] using ht

set_option maxRecDepth 4096 in
theorem cfg_fn (hp : VPre PlannerRunView PlannerRunG.Ok P g F plannerRunA plannerRunD s) :
    plannerRunAsm.ForallBlocks fun blk =>
      blk.label = .label Names.plannerRun → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl, Names.plannerRun]
  intro t ht
  simp only [RunInv, Names.plannerRun, ↓reduceIte] at ht
  subst t
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label Names.plannerRun) 1 (s.pushRa ra) b j u
  have hh := b_fn P g F s ra hp (I' (.label ".LB.Planner.run.0") 2)
    I' (RunExit P g F s ra) (by
      intro u hu
      apply Program.Intercept.intro_label (i := 2) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte]
        have hm := Nat.mul_le_mul_right (g.p.m.toNat + 4)
          (Nat.sub_le g.p.n.toNat (rcx u).toNat)
        simp only [Nat.add_mul, Nat.one_mul]
        omega) (by
      intro u hu
      apply Program.Intercept.intro_label (i := 5) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte]
        have hm : 0 < (g.p.n.toNat + 1) * (g.p.m.toNat + 4) :=
          Nat.mul_pos (by omega) (by omega)
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, Names.plannerRun, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh

set_option maxRecDepth 4096 in
theorem cfg_1 (hok : g.Ok) : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.1" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.1") 3 t b j u
  have hh := b_1 P (withSaw g 0#8) F s t ra (withSaw_ok hok _)
    (I' (.label ".LB.Planner.run.2") 4) I' (RunExit P g F s ra) (by
      intro u he hu
      apply Program.Intercept.intro_label (i := 1) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, he]
        omega) (by
      intro u he hu
      apply Program.Intercept.intro_label (i := 4) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, he]
        omega) (by
      intro u he hz hu
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, he, hz,
          BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_2 (hok : g.Ok) : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.2" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.2") 4 t b j u
  have hh := b_2 P (withSaw g 0#8) F s t ra (withSaw_ok hok _)
    (I' (.label ".LB.Planner.run.3") 5) I' (RunExit P g F s ra) (by
      intro u he hu
      apply Program.Intercept.intro_label (i := 1) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, he]
        omega) (by
      intro u hc ha hu
      apply Program.Intercept.intro_label (i := 3) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.toBd.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · have hi := ht.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1
        have hui := hu.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1
        change rax t < g.p.m at hi
        change rax u < g.p.m at hui
        have hs : (rax u).toNat = (rax t).toNat + 1 := by rw [ha]; bv_omega
        simp only [runV, String.reduceEq, or_false, ↓reduceIte, hc, hs]
        change (rax t).toNat < g.p.m.toNat at hi
        change (rax u).toNat < g.p.m.toNat at hui
        omega) (by
      intro u he hu
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, or_true, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, he]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

end
end Bbu.Unit.PlannerRunU
