module

public import FlatShuffler.Unit.Plan.PlannerRunCfgDefs
import all FlatShuffler.Unit.Plan.PlannerRunCfgDefs
public import FlatShuffler.Unit.Plan.PlannerRunEmissionCopy
import all FlatShuffler.Unit.Plan.PlannerRunEmissionCopy
public import FlatShuffler.Unit.Plan.PlannerRunEmissionDest
import all FlatShuffler.Unit.Plan.PlannerRunEmissionDest
public import FlatShuffler.Unit.Plan.PlannerRunEmissionPosStart
import all FlatShuffler.Unit.Plan.PlannerRunEmissionPosStart
public import FlatShuffler.Unit.Plan.PlannerRunEmissionPos
import all FlatShuffler.Unit.Plan.PlannerRunEmissionPos
public import FlatShuffler.Unit.Plan.PlannerRunEmissionCountAdvance
import all FlatShuffler.Unit.Plan.PlannerRunEmissionCountAdvance
public import FlatShuffler.Unit.Plan.PlannerRunEmissionCount
import all FlatShuffler.Unit.Plan.PlannerRunEmissionCount
public import FlatShuffler.Unit.Plan.PlannerRunEmissionEmpty
import all FlatShuffler.Unit.Plan.PlannerRunEmissionEmpty
public import FlatShuffler.Unit.Plan.PlannerRunEmissionZero
import all FlatShuffler.Unit.Plan.PlannerRunEmissionZero

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

private theorem same_budget {initial current : PlannerCallMemory} {P : Addr} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals lo' locals' : List Word}
    (hmeta : RunMeta initial current) (ht : Bd P current F s ra lo locals t)
    (hu : Bd P current F s ra lo' locals' u) : dropBudget initial u = dropBudget initial t :=
  (dropBudget_eq hmeta hu.kb.vmem).trans (dropBudget_eq hmeta ht.kb.vmem).symm

private theorem indexAt_eq {base : Addr} {t : MachineData} {j : Word}
    (ha : rax t = base + j * 8#64) (hj : j.toNat < 1024) : indexAt base t = j.toNat := by
  have hd : rax t - base = j * 8#64 := by rw [ha]; bv_omega
  have hm : (j * 8#64).toNat = j.toNat * 8 := by bv_omega
  rw [indexAt, hd, hm]
  omega

section
variable [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)

set_option maxRecDepth 4096 in
theorem cfg_10 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.24" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hi := ht.choose_spec.choose_spec.2.1
  have hm := congrArg PlannerObjectMemory.sourceSize ctx.stable.planner
  change current.p.sourceSize = g.p.sourceSize at hm
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.24") 26 t b j u
  have hh := b_10 P current M F s t ra ctx.ok ctx.wanted
    (I' (.label ".LB.Planner.run.25") 27) I' (RunExit P g F s ra) (by
      intro data u ha hu
      have h1 := hu.choose_spec.choose_spec.1
      have hui := hu.choose_spec.choose_spec.2.1
      have hb := (dropBudget_eq (ctx.stable.withData data) h1.kb.vmem).trans
        (dropBudget_eq ctx.stable h0.kb.vmem).symm
      apply Program.Intercept.intro_label (i := 25)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show ∃ a M, ∃ c : AttemptContext g a s M,
            EmitDataHead P a M F s ra c.wanted u from
            ⟨{current with data := data}, M, ctx.withData data, hu⟩)
      · have hiN : (rax t).toNat < 1024 :=
          Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) ctx.ok.planner.sourceSizeFitsBuffer
        have hs : (rax u).toNat = (rax t).toNat + 1 := by rw [ha]; bv_omega
        simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hs]
        change rax u < current.p.sourceSize at hui
        rw [hm] at hi hui
        change (rax t).toNat < g.p.sourceSize.toNat at hi
        change (rax u).toNat < g.p.sourceSize.toNat at hui
        omega) (by
      intro data u hd hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := (dropBudget_eq (ctx.stable.withData data) h1.kb.vmem).trans
        (dropBudget_eq ctx.stable h0.kb.vmem).symm
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitDestHead P a M F s ra) u from
            ⟨{current with data := data}, M, ctx.withData data, hd, hu⟩)
      · have hmb : g.p.sourceSize.toNat ≤ 1024 := by rw [← hm]; exact ctx.ok.planner.sourceSizeFitsBuffer
        simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_11 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.25" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hi := ht.choose_spec.choose_spec.2.1
  have hm := congrArg PlannerObjectMemory.sourceSize ctx.stable.planner
  change current.p.sourceSize = g.p.sourceSize at hm
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.25") 27 t b j u
  have hh := b_11 P current M F s t ra ctx.ok (I' (.label ".LB.Planner.run.26") 28)
    I' (RunExit P g F s ra) (by
      intro u ha hu
      have h1 := hu.choose_spec.choose_spec.1
      have hui := hu.choose_spec.choose_spec.2.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 26)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitDestHead P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · have hiN : (rax t).toNat < 1024 :=
          Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) ctx.ok.planner.sourceSizeFitsBuffer
        have hs : (rax u).toNat = (rax t).toNat + 1 := by rw [ha]; bv_omega
        simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hs]
        rw [hm] at hi hui
        change (rax t).toNat < g.p.sourceSize.toNat at hi
        change (rax u).toNat < g.p.sourceSize.toNat at hui
        omega) (by
      intro u ha hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitDestDone P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_12 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.26" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hn := congrArg PlannerObjectMemory.targetSize ctx.stable.planner
  change current.p.targetSize = g.p.targetSize at hn
  have hnb : g.p.targetSize.toNat ≤ 1024 := by rw [← hn]; exact ctx.ok.planner.targetSizeFitsBuffer
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.26") 28 t b j u
  have hh := b_12 P current M F s ra (I' (.label ".LB.Planner.run.27") 29)
    I' (RunExit P g F s ra) (by
      intro u hz hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 15)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s
            (fun a M u => a.p.targetSize = 0#64 ∧ EmitMapped P a M F s ra u) u from
            ⟨current, M, ctx, hd, hz, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitPosHead P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 4096 in
theorem cfg_13 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.27" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  obtain ⟨lo, locals, j, h0, hj, hax, hrest⟩ := ht
  have hn := congrArg PlannerObjectMemory.targetSize ctx.stable.planner
  change current.p.targetSize = g.p.targetSize at hn
  have hjN : j.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) ctx.ok.planner.targetSizeFitsBuffer
  have hi : indexAt 0#64 t = j.toNat := indexAt_eq (by simpa only [BitVec.zero_add] using hax) hjN
  have hnb : g.p.targetSize.toNat ≤ 1024 := by rw [← hn]; exact ctx.ok.planner.targetSizeFitsBuffer
  let I' (b : CfgLabel) (k : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.27") 29 t b k u
  have hh := b_13 P current M F s t ra ctx.ok (I' (.label ".LB.Planner.run.28") 30)
    I' (RunExit P g F s ra) (by
      intro u ha hu
      obtain ⟨lo', locals', j', h1, hj', hax', hrest'⟩ := hu
      have hjN' : j'.toNat < 1024 :=
        Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj') ctx.ok.planner.targetSizeFitsBuffer
      have hi' : indexAt 0#64 u = j'.toNat :=
        indexAt_eq (by simpa only [BitVec.zero_add] using hax') hjN'
      have hstep : j'.toNat = j.toNat + 1 := by rw [hax, hax'] at ha; bv_omega
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 28)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitPosHead P a M F s ra) u from
            ⟨current, M, ctx, hd, lo', locals', j', h1, hj', hax', hrest'⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hi, hi', hstep]
        rw [hn] at hj hj'
        change j.toNat < g.p.targetSize.toNat at hj
        change j'.toNat < g.p.targetSize.toNat at hj'
        omega) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 9)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitCountHead P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ⟨lo, locals, j, h0, hj, hax, hrest⟩

set_option maxRecDepth 4096 in
theorem cfg_14 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.7" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  obtain ⟨lo, locals, j, c, h0, hj, hax, hrest⟩ := ht
  have hn := congrArg PlannerObjectMemory.targetSize ctx.stable.planner
  change current.p.targetSize = g.p.targetSize at hn
  have hjN : j.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) ctx.ok.planner.targetSizeFitsBuffer
  have hi := indexAt_eq hax hjN
  let I' (b : CfgLabel) (k : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.7") 9 t b k u
  have hh := b_14 P current M F s t ra ctx.ok (I' (.label ".LB.Planner.run.8") 10)
    I' (RunExit P g F s ra) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 16)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitReady P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega) (by
      intro u ha hu
      obtain ⟨lo', locals', j', c', h1, hj', hax', hrest'⟩ := hu
      have hjN' : j'.toNat < 1024 :=
        Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj') ctx.ok.planner.targetSizeFitsBuffer
      have hi' := indexAt_eq hax' hjN'
      have hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec := h1.kb.sp.trans h0.kb.sp.symm
      have hstep : j'.toNat = j.toNat + 1 := by rw [hax, hax', hsp] at ha; bv_omega
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitCountHead P a M F s ra) u from
            ⟨current, M, ctx, hd, lo', locals', j', c', h1, hj', hax', hrest'⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hi, hi', hstep]
        rw [hn] at hj hj'
        change j.toNat < g.p.targetSize.toNat at hj
        change j'.toNat < g.p.targetSize.toNat at hj'
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ⟨lo, locals, j, c, h0, hj, hax, hrest⟩

set_option maxRecDepth 4096 in
theorem cfg_15 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.8" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  obtain ⟨lo, locals, j, c, h0, hj, hax, hrest⟩ := ht
  have hjN : j.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) ctx.ok.planner.targetSizeFitsBuffer
  have hi := indexAt_eq hax hjN
  let I' (b : CfgLabel) (k : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.8") 10 t b k u
  have hh := b_15 P current M F s t ra ctx.ok (I' (.label ".LB.Planner.run.9") 11)
    I' (RunExit P g F s ra) (by
      intro u ha hu
      obtain ⟨lo', locals', j', c', h1, hj', hax', hrest'⟩ := hu
      have hjN' : j'.toNat < 1024 :=
        Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj') ctx.ok.planner.targetSizeFitsBuffer
      have hi' := indexAt_eq hax' hjN'
      have hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec := h1.kb.sp.trans h0.kb.sp.symm
      have heq : j' = j := by rw [hax, hax', hsp] at ha; bv_omega
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 8)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitCountNext P a M F s ra) u from
            ⟨current, M, ctx, hd, lo', locals', j', c', h1, hj', hax', hrest'⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hi, hi', heq]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ⟨lo, locals, j, c, h0, hj, hax, hrest⟩

set_option maxRecDepth 4096 in
theorem cfg_27 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.14" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, hn, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.14") 16 t b j u
  have hh := b_27 P current M F s ra ctx.ok hn (I' (.label ".LB.Planner.run.15") 17)
    I' (RunExit P g F s ra) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitReady P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 4096 in
theorem cfg_32 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.28" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M, ctx, hd, hm, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.28") 30 t b j u
  have hh := b_32 P current M F s ra ctx.ok hm
    (fun _ u => RunInv P g F s ra resolvePhase .exit u)
    I' (RunExit P g F s ra) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 27)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M => EmitDestDone P a M F s ra) u from
            ⟨current, M, ctx, hd, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, true_and] at hh
  exact hh t ht

end
end FlatShuffler.Unit.PlannerRunU
