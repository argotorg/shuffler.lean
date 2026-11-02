module

public import FlatShuffler.Unit.Plan.PlannerRunCfgDefs
import all FlatShuffler.Unit.Plan.PlannerRunCfgDefs
public import FlatShuffler.Unit.Plan.PlannerRunInitStart
import all FlatShuffler.Unit.Plan.PlannerRunInitStart
public import FlatShuffler.Unit.Plan.PlannerRunInitDest
import all FlatShuffler.Unit.Plan.PlannerRunInitDest
public import FlatShuffler.Unit.Plan.PlannerRunInitPosStart
import all FlatShuffler.Unit.Plan.PlannerRunInitPosStart
public import FlatShuffler.Unit.Plan.PlannerRunInitPos
import all FlatShuffler.Unit.Plan.PlannerRunInitPos

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

private theorem index_at {base i : Word} {t : MachineData} (hi : i.toNat ≤ 1024)
    (ha : rax t = base + i * 8#64) : indexAt base t = i.toNat := by
  unfold indexAt
  rw [ha]
  have hw : (base + i * 8#64 - base).toNat = i.toNat * 8 := by bv_omega
  rw [hw]
  omega

section
variable [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)

set_option maxRecDepth 4096 in
theorem cfg_5 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.19" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, hok, ⟨ctx⟩, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hm := congrArg PlannerObjectMemory.sourceSize ctx.stable.planner
  change current.p.sourceSize = g.p.sourceSize at hm
  have hmb : g.p.sourceSize.toNat ≤ 1024 := by rw [← hm]; exact hok.planner.sourceSizeFitsBuffer
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.19") 21 t b j u
  have hh := b_5 P current F s ra (I' (.label ".LB.Planner.run.20") 22)
    I' (RunExit P g F s ra) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 22)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitDestDone P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega) (by
      intro u ha hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitDestHead P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, ha, BitVec.toNat_ofNat]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 4096 in
theorem cfg_8 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.22" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, hok, ⟨ctx⟩, ht⟩ := ht
  obtain ⟨lo, locals, i, h0, hi, ha, rest⟩ := ht
  have ht : InitPosHead P current F s ra t := ⟨lo, locals, i, h0, hi, ha, rest⟩
  have hn := congrArg PlannerObjectMemory.targetSize ctx.stable.planner
  change current.p.targetSize = g.p.targetSize at hn
  have hiN : i.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hok.planner.targetSizeFitsBuffer
  have hix := index_at (by omega : i.toNat ≤ 1024) ha
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.22") 24 t b j u
  have hh := b_8 P current F s t ra hok (I' (.label ".LB.Planner.run.23") 25)
    I' (RunExit P g F s ra) (by
      intro u hau hu
      obtain ⟨lo', locals', j, h1, hj, haj, rest'⟩ := hu
      have hu : InitPosHead P current F s ra u := ⟨lo', locals', j, h1, hj, haj, rest'⟩
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      have hjN : j.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hj) hok.planner.targetSizeFitsBuffer
      have hjx := index_at (by omega : j.toNat ≤ 1024) haj
      have hs : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec := h1.kb.sp.trans h0.kb.sp.symm
      have hij : j.toNat = i.toNat + 1 := by
        rw [hau, ha, hs] at haj
        bv_omega
      apply Program.Intercept.intro_label (i := 23)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitPosHead P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hix, hjx]
        have hin := BitVec.lt_def.mp hi
        have hjn := BitVec.lt_def.mp hj
        rw [hn] at hin hjn
        omega) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitDone P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_6 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.20" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, hok, ⟨ctx⟩, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hi := ht.choose_spec.choose_spec.2.1
  have hm := congrArg PlannerObjectMemory.sourceSize ctx.stable.planner
  change current.p.sourceSize = g.p.sourceSize at hm
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.20") 22 t b j u
  have hh := b_6 P current F s t ra hok (I' (.label ".LB.Planner.run.21") 23)
    I' (RunExit P g F s ra) (by
      intro u ha hu
      have h1 := hu.choose_spec.choose_spec.1
      have hui := hu.choose_spec.choose_spec.2.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 21)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitDestHead P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · have hiN : (rax t).toNat < 1024 :=
          Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) hok.planner.sourceSizeFitsBuffer
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
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitDestDone P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_7 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.21" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, hok, ⟨ctx⟩, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hn := congrArg PlannerObjectMemory.targetSize ctx.stable.planner
  change current.p.targetSize = g.p.targetSize at hn
  have hnb : g.p.targetSize.toNat ≤ 1024 := by rw [← hn]; exact hok.planner.targetSizeFitsBuffer
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.21") 23 t b j u
  have hh := b_7 P current F s ra (I' (.label ".LB.Planner.run.22") 24)
    I' (RunExit P g F s ra) (by
      intro u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 24)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitDone P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega) (by
      intro u ha hu
      have h1 := hu.choose_spec.choose_spec.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] using
          (show LoopPhase g s (fun a => InitPosHead P a F s ra) u from
            ⟨current, hok, ⟨ctx⟩, hu⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, indexAt, ha,
          BitVec.sub_self, BitVec.toNat_zero, Nat.zero_div, Nat.sub_zero]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 4096 in
theorem cfg_9
    (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit")
    (hip : BSpecWithExit Names.mapInPlace mapInPlaceA 6 mapInPlaceQ mapInPlaceX)
    (hclosest : BSpecWithExit Names.mapClosestCopies mapClosestA 8 mapClosestQ mapClosestX)
    (hwild : BSpecWithExit Names.mapWildcardSlotCopies mapWildA 10 mapWildQ mapWildX)
    (hkeep : BSpecWithExit Names.keepWildcardSlots keepWildA 6 keepWildQ keepWildX)
    (habsorb : BSpecWithExit Names.absorbSurplus absorbA 6 absorbQ absorbX) :
    plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.23" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, hok, ⟨ctx⟩, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  have hsize := congrArg PlannerObjectMemory.sourceSize ctx.stable.planner
  change current.p.sourceSize = g.p.sourceSize at hsize
  have hmb : g.p.sourceSize.toNat ≤ 1024 := by rw [← hsize]; exact hok.planner.sourceSizeFitsBuffer
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.23") 25 t b j u
  have hh := b_9 P current F s ra hok hip hclosest hwild hkeep habsorb
    (I' (.label ".LB.Planner.run.24") 26) I' (RunExit P g F s ra) (by
      intro M0 u hu
      have h1 := hu.choose_spec.choose_spec.1
      have hphase : BuildFailPhase P g F s ra u := ⟨current, M0, hok, ⟨ctx⟩, hu⟩
      apply Program.Intercept.intro_label (i := 7) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false,
          ↓reduceIte] using hphase
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        omega) (by
      intro M0 u hx harg
      obtain ⟨lo, locals, hlo, hlocals, hmem, hinit, hfail⟩ := hx
      let v : MachineData := {u with regs := {u.regs with rax := ⟨2#64⟩}}
      have hq := ctx.mapping_fail (t := v) hok M0 hinit hfail rfl
      refine Or.inr ⟨Or.inr ⟨rfl, harg, current, plannerRunX_of_Q hq rfl, hok,
        fr s lo locals, ra.toBitVec, ?_, hmem⟩, ?_⟩
      · simp [fr, saved, hlo, hlocals, plannerRunD]
      · intro l hl heq
        exact False.elim (hout l hl heq)) (by
      intro u hz hu
      obtain ⟨M0, M, saw, lo, locals, h1, hm, hi, hb, htargets⟩ := hu
      let ctx' := AttemptContext.ofBuild ctx hok M0 M saw hm hi hb htargets
      have hbudget : dropBudget g u = dropBudget g t := by
        rw [dropBudget_eq ctx'.stable h1.kb.vmem,
          dropBudget_eq ctx.stable h0.kb.vmem]
        rfl
      have hd : (withSaw current (mergeSaw current.p.saw saw)).state.data = ctx'.wanted := by
        change current.state.data = Flat.copyFrom current.p.fl 0 current.state.data
        have hn : ¬ (0 : Word) < current.p.fl.sourceSize := by
          change ¬ (0 : Word) < current.p.sourceSize
          rw [hz]
          exact BitVec.lt_irrefl _
        rw [Flat.copyFrom]
        split
        · rename_i hlt
          exact False.elim (hn hlt)
        · rfl
      apply Program.Intercept.intro_label (i := 29) (by decide)
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte] using
          (show AttemptPhase g s (fun a M u => a.p.sourceSize = 0#64 ∧
            ∃ lo locals, AttemptLI P a M F s ra lo locals u) u from
            ⟨withSaw current (mergeSaw current.p.saw saw), M, ctx', hd, hz,
              lo, locals, h1⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hbudget]
        omega) (by
      intro u hn ha hu
      obtain ⟨M0, M, saw, lo, locals, h1, hm, hi, hb, htargets⟩ := hu
      let ctx' := AttemptContext.ofBuild ctx hok M0 M saw hm hi hb htargets
      have hbudget : dropBudget g u = dropBudget g t := by
        rw [dropBudget_eq ctx'.stable h1.kb.vmem,
          dropBudget_eq ctx.stable h0.kb.vmem]
        rfl
      refine ⟨?_, Or.inl ?_⟩
      · simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte]
        refine ⟨withSaw current (mergeSaw current.p.saw saw), M, ctx', lo, locals,
          h1, ?_, ?_⟩
        · rw [ha]
          change 0#64 < current.p.sourceSize
          bv_omega
        · rw [ha]
          rfl
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hbudget, ha,
          BitVec.toNat_zero, Nat.sub_zero]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

end
end FlatShuffler.Unit.PlannerRunU
