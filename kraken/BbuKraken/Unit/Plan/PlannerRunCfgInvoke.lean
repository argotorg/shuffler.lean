module

public import BbuKraken.Unit.Plan.PlannerRunCfgResolveDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgResolveDefs
public import BbuKraken.Unit.Plan.PlannerRunEmissionInvoke
import all BbuKraken.Unit.Plan.PlannerRunEmissionInvoke
public import BbuKraken.Unit.Plan.PlannerRunEmissionBlocked
import all BbuKraken.Unit.Plan.PlannerRunEmissionBlocked

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

set_option maxRecDepth 8192 in
theorem cfg_28 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64)
    (hrun : ∀ PM planned, VSpec (RunView PM planned) G.Ok Names.run
      (runA planned) runD (runQ planned)) :
    plannerRunAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Planner.run.28" → FullRunObl P g F s ra blk := by
  cfg_view as hv
  cfg_block [FullRunObl, RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false,
    ↓reduceIte, AttemptPhase] at ht
  obtain ⟨current, M, ctx, hd, ht⟩ := ht
  have h0 := ht.choose_spec.choose_spec.1
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    FullRunInv P g F s ra b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.28") 30 t b j u
  have hh := b_28 P current M F s ra ctx.ok ctx.map hrun
    (I' (.label ".LB.Planner.run.29") 31) I' (RunExit P g F s ra) (by
      intro v lo locals hc hp a hk u lo' hpost hq ha hag
      obtain ⟨ec, hal, hout⟩ := ctx.afterEmission hd hc hp a hk hq
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
              (newg.p.m - Flat.droppedCount newg.p.m newg.dropped).toNat :=
            dropBudget_eq ec.stable hw.kb.vmem
          _ = (current.p.m - Flat.droppedCount current.p.m current.dropped).toNat := rfl
          _ = dropBudget g t := (dropBudget_eq ctx.stable h0.kb.vmem).symm
      refine ⟨?_, ?_, ?_⟩
      · intro w hw hpres hn
        have hnb : ec.status ≠ .blocked := by
          intro he
          apply hn
          rw [hpres, hal, he]
          rfl
        apply Program.Intercept.intro_label (i := 17) (by decide)
        left
        refine ⟨hw.kb.stack (by decide), ?_, Or.inl ?_⟩
        · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq,
            ↓reduceIte, EmittedPhase]
          exact ⟨newg, M, ec, hpres.trans hal, hnb, lo', ls, hw⟩
        · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
          omega
      · intro w hw he hz hbp
        have hs : ec.status = .blocked := (code_blocked_iff _).mp (hal.symm.trans he)
        have bounds := hc.blockedBounds ctx.ok ctx.map hp a hq he
        have restored : BlockedBounds newg.p.n ec.out := by
          rw [hout]
          exact ⟨bounds.size, bounds.offset, bounds.excess, bounds.current⟩
        have inputs : ResolveInputs newg M ls hpost.localLength := by
          apply cells.resolveInputs
          · exact restored
          · exact ctx.map
        have hb := hbudget w hw
        apply Program.Intercept.intro_label (i := 31) (by decide)
        left
        refine ⟨hw.kb.stack (by decide), ?_, Or.inl ?_⟩
        · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false,
            ↓reduceIte, RunResolvePhase]
          refine ⟨newg, M, ls, hpost.localLength, ec, hs, cells, inputs, lo',
            ⟨hw, ec.targets⟩, ?_⟩
          rw [hbp]
          change 0#64 = Flat.droppedCount newg.p.m newg.dropped
          rw [hz, Flat.droppedCount, dropped_end (by decide)]
          rfl
        · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
          omega
      · intro w hw he hn hbp hax hdx
        have hs : ec.status = .blocked := (code_blocked_iff _).mp (hal.symm.trans he)
        have bounds := hc.blockedBounds ctx.ok ctx.map hp a hq he
        have restored : BlockedBounds newg.p.n ec.out := by
          rw [hout]
          exact ⟨bounds.size, bounds.offset, bounds.excess, bounds.current⟩
        have inputs : ResolveInputs newg M ls hpost.localLength := by
          apply cells.resolveInputs
          · exact restored
          · exact ctx.map
        have hb := hbudget w hw
        refine ⟨?_, Or.inl ?_⟩
        · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false,
            ↓reduceIte, RunResolvePhase]
          refine ⟨newg, M, ls, hpost.localLength, ec, hs, cells, inputs,
            lo', 0#64, ⟨hw, ec.targets⟩, ?_, ?_, hdx, ?_⟩
          · change 0#64 < newg.p.m
            change newg.p.m ≠ 0#64 at hn
            bv_omega
          · simpa using hax
          · rw [hbp]
            rfl
        · have hm := congrArg PG.m ctx.stable.planner
          change current.p.m = g.p.m at hm
          have hmb : g.p.m.toNat ≤ 1024 := by rw [← hm]; exact ctx.ok.planner.m
          simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
          omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

end Bbu.Unit.PlannerRunU
