module

public import FlatShuffler.Unit.Plan.PlannerRunCfgResolveDefs
import all FlatShuffler.Unit.Plan.PlannerRunCfgResolveDefs
public import FlatShuffler.Unit.Plan.PlannerRunEmissionInvoke
import all FlatShuffler.Unit.Plan.PlannerRunEmissionInvoke
public import FlatShuffler.Unit.Plan.PlannerRunEmissionBlocked
import all FlatShuffler.Unit.Plan.PlannerRunEmissionBlocked

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

set_option maxRecDepth 8192 in
theorem cfg_28 [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64)
    (hout : ∀ l ∈ Program.labels plannerRunAsm, label l ≠ label "exit")
    (hrun : ∀ PM planned, VSpecWithExit (RunView PM planned) G.Ok Names.run
      (runA planned) runD (runQ planned) (runX planned)) :
    plannerRunAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Planner.run.15" → FullRunObl P g F s ra blk := by
  cfg_view as hv
  cfg_block [FullRunObl, RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq,
    ↓reduceIte, AttemptPhase] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    FullRunInv P g F s ra b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.15") 17 t b j u
  have hh := b_28 P current M F s ra ctx.ok ctx.map hrun
    (I' (.label ".LB.Planner.run.16") 18) I' (RunExit P g F s ra) (by
      intro v lo locals hc hp a hk u lo' hpost hq ha hag
      obtain ⟨ec, hal, hout⟩ := ctx.afterEmission hd hc hp a hk hq
      have statusIsNormal : ec.status ≠ .assertionExit := by
        intro failed
        have impossible := hal
        rw [failed, code_assertionExit] at impossible
        contradiction
      let newg := emissionResult current ctx.ok (localEmissionHdr locals hc.localLength) a hk
      let ls := (EmissionLocals.ofList locals hc.localLength).toList a.h
        (v.regs.rsp.toBitVec + 96#64)
      have cells : EmissionCells ls hpost.localLength ec.out := by
        rw [hout]
        have hc := EmissionLocals.cells (EmissionLocals.ofList locals hc.localLength)
          a (v.regs.rsp.toBitVec + 96#64) hpost.localLength
        exact ⟨hc.size, hc.offset, hc.excess, hc.current⟩
      have hbudget (w : MachineData) (hw : PostEmitLI P newg M F s ra lo' ls w) :
          dropBudget g w = dropBudget g t := by
        calc
          dropBudget g w =
              (newg.p.sourceSize - Flat.droppedCount newg.p.sourceSize newg.dropped).toNat :=
            dropBudget_eq ec.stable hw.kb.vmem
          _ = (current.p.sourceSize - Flat.droppedCount current.p.sourceSize current.dropped).toNat := rfl
          _ = dropBudget g t := (dropBudget_eq ctx.stable h0.kb.vmem).symm
      refine ⟨?_, ?_, ?_⟩
      · intro w hw hpres hn
        have hnb : ec.status ≠ .blocked := by
          intro he
          apply hn
          exact Option.some.inj ((congrArg some hpres).trans
            (hal.trans (congrArg code he)))
        apply Program.Intercept.intro_label (i := 10) (by decide)
        left
        refine ⟨hw.kb.stack (by decide), ?_, Or.inl ?_⟩
        · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq,
            ↓reduceIte, EmittedPhase]
          exact ⟨newg, M, ec, (congrArg some hpres).trans hal, hnb, statusIsNormal, lo', ls, hw⟩
        · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
          omega
      · intro w hw he hz hbp
        have hs : ec.status = .blocked := (code_blocked_iff _).mp (hal.symm.trans (congrArg some he))
        have bounds := hc.blockedBounds ctx.ok ctx.map hp a hq he
        have restored : BlockedBounds newg.p.targetSize ec.out := by
          rw [hout]
          exact ⟨bounds.size, bounds.offset, bounds.excess, bounds.current⟩
        have inputs : ResolveInputs newg M ls hpost.localLength := by
          apply cells.resolveInputs
          · exact restored
          · exact ctx.map
        have hb := hbudget w hw
        apply Program.Intercept.intro_label (i := 18) (by decide)
        left
        refine ⟨hw.kb.stack (by decide), ?_, Or.inl ?_⟩
        · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq,
            ↓reduceIte, RunResolvePhase]
          refine ⟨newg, M, ls, hpost.localLength, ec, hs, cells, inputs, lo',
            ⟨hw, ec.targets⟩, ?_⟩
          rw [hbp]
          change 0#64 = Flat.droppedCount newg.p.sourceSize newg.dropped
          rw [hz, Flat.droppedCount, dropped_end (by decide)]
          rfl
        · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
          omega
      · intro w hw he hn hbp hax hdx
        have hs : ec.status = .blocked := (code_blocked_iff _).mp (hal.symm.trans (congrArg some he))
        have bounds := hc.blockedBounds ctx.ok ctx.map hp a hq he
        have restored : BlockedBounds newg.p.targetSize ec.out := by
          rw [hout]
          exact ⟨bounds.size, bounds.offset, bounds.excess, bounds.current⟩
        have inputs : ResolveInputs newg M ls hpost.localLength := by
          apply cells.resolveInputs
          · exact restored
          · exact ctx.map
        have hb := hbudget w hw
        refine ⟨?_, Or.inl ?_⟩
        · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq,
            ↓reduceIte, RunResolvePhase]
          refine ⟨newg, M, ls, hpost.localLength, ec, hs, cells, inputs,
            lo', 0#64, ⟨hw, ec.targets⟩, ?_, ?_, hdx, ?_⟩
          · change 0#64 < newg.p.sourceSize
            change newg.p.sourceSize ≠ 0#64 at hn
            bv_omega
          · simpa using hax
          · rw [hbp]
            rfl
        · have hm := congrArg PlannerObjectMemory.sourceSize ctx.stable.planner
          change current.p.sourceSize = g.p.sourceSize at hm
          have hmb : g.p.sourceSize.toNat ≤ 1024 := by rw [← hm]; exact ctx.ok.planner.sourceSizeFitsBuffer
          simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
          omega) (by
      intro v lo locals hc hp a hk u lo' hl hm hx ha harg
      refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
      · refine ⟨_, ctx.afterEmissionExit hd hc hp a hk hx,
          emissionResult_ok ctx.ok _ hk ha, ?_⟩
        refine ⟨fr s lo' ((EmissionLocals.ofList locals hc.localLength).toList a.h
          (v.regs.rsp.toBitVec + 96#64)), ra.toBitVec, ?_, hm⟩
        simp only [fr, saved, List.length_append, List.length_cons, List.length_nil,
          hl, EmissionLocals.length, plannerRunD]
      · intro l hl ha
        exact False.elim (hout l hl ha))
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

end FlatShuffler.Unit.PlannerRunU
