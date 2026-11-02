module

public import BbuKraken.Unit.Plan.PlannerRunCfgResolveDefs
import all BbuKraken.Unit.Plan.PlannerRunCfgResolveDefs
public import BbuKraken.Unit.Plan.PlannerRunResolve
import all BbuKraken.Unit.Plan.PlannerRunResolve
public import BbuKraken.Unit.Plan.PlannerRunResolveTargets
import all BbuKraken.Unit.Plan.PlannerRunResolveTargets

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

private theorem same_budget {initial current : PlannerRunG} {P : Addr} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo locals lo' locals' : List Word}
    (hmeta : RunMeta initial current) (ht : Bd P current F s ra lo locals t)
    (hu : Bd P current F s ra lo' locals' u) : dropBudget initial u = dropBudget initial t :=
  (dropBudget_eq hmeta hu.kb.vmem).trans (dropBudget_eq hmeta ht.kb.vmem).symm

section
variable [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64)

set_option maxRecDepth 4096 in
theorem cfg_29 : plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.28" → FullRunObl P g F s ra blk := by
  cfg_view as hv
  cfg_block [FullRunObl, RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte,
    RunResolvePhase] at ht
  obtain ⟨current, M, locals, hl, ctx, hblocked, hcells, hin, ht⟩ := ht
  obtain ⟨lo, i, h0, hi, hax, hrest⟩ := ht
  have hm := congrArg PG.m ctx.stable.planner
  change current.p.m = g.p.m at hm
  have hp := congrArg PG.drp ctx.stable.planner
  change current.p.drp = g.p.drp at hp
  have hiN : i.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) h0.ok.planner.m
  have hidx : (rax t - g.p.drp).toNat = i.toNat := by
    have he : rax t - g.p.drp = i := by rw [hax, hp]; bv_omega
    rw [he]
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    FullRunInv P g F s ra b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.28") 30 t b j u
  have hh := b_29_fixed P current M F s t ra locals (I' (.label ".LB.Planner.run.29") 31)
    I' (RunExit P g F s ra) (by
      intro u ha hu
      obtain ⟨lo', i', h1, hi', hax', hrest'⟩ := hu
      have hiN' : i'.toNat < 1024 := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi') h0.ok.planner.m
      have hidx' : (rax u - g.p.drp).toNat = i'.toNat := by
        have he : rax u - g.p.drp = i' := by rw [hax', hp]; bv_omega
        rw [he]
      have hs : i'.toNat = i.toNat + 1 := by rw [hax, hax'] at ha; bv_omega
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      apply Program.Intercept.intro_label (i := 29)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false,
          ↓reduceIte, RunResolvePhase]
        refine ⟨current, M, locals, hl, ctx, hblocked, hcells, hin, ?_⟩
        simpa only [String.reduceEq, ↓reduceIte] using
          (show DropBeforeFixed P current M F s ra locals u from
            ⟨lo', i', h1, hi', hax', hrest'⟩)
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hidx, hidx', hs]
        rw [hm] at hi hi'
        change i.toNat < g.p.m.toNat at hi
        change i'.toNat < g.p.m.toNat at hi'
        omega) (by
      intro u hu
      have h1 := hu.choose_spec.1
      have hb := same_budget ctx.stable h0.toBd h1.toBd
      refine ⟨?_, Or.inl ?_⟩
      · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false,
          ↓reduceIte, RunResolvePhase]
        refine ⟨current, M, locals, hl, ctx, hblocked, hcells, hin, ?_⟩
        simpa only [String.reduceEq, ↓reduceIte] using hu
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ⟨lo, i, h0, hi, hax, hrest⟩

set_option maxRecDepth 4096 in
theorem cfg_30 (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit")
    (hresolve : VSpecWithExit RView RG.Ok Names.resolve resolveA 1182 resolveQ resolveX) :
    plannerRunAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.run.29" → FullRunObl P g F s ra blk := by
  cfg_view as hv
  cfg_block [FullRunObl, RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte,
    RunResolvePhase] at ht
  obtain ⟨current, M, locals, hl, ctx, hblocked, hcells, hin, ht⟩ := ht
  obtain ⟨lo, h0, hbp⟩ := ht
  let scratch : Flat.ResolveU := ⟨Vector.replicate MAX_N 0#8, Vector.replicate MAX_N 0#64⟩
  let before := Flat.droppedCount current.p.m current.dropped
  have hm := congrArg PG.m ctx.stable.planner
  change current.p.m = g.p.m at hm
  have hp := congrArg PG.drp ctx.stable.planner
  change current.p.drp = g.p.drp at hp
  have hmb : g.p.m.toNat ≤ 1024 := by rw [← hm]; exact h0.ok.planner.m
  have hb := dropBudget_eq ctx.stable h0.kb.vmem
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    FullRunInv P g F s ra b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.29") 31 t b j u
  have hh := b_30 P current M F s ra locals hl hin before hresolve
    (I' (.label ".LB.Planner.run.30") 32) I' (RunExit P g F s ra) (by
      intro spills dropped res lo' u hr h1 hres hal
      have hmodel := hcells.resolved hr scratch
      let rc := ctx.afterResolve hblocked scratch res spills dropped hmodel
      have hres' : rc.resolution ≠ .dropped := hres
      have hcode : ResolveU.code res = code (if res = .stuck then .blocked else .assertionFailed) := by
        cases res with
        | dropped => exact False.elim (hres rfl)
        | stuck => rfl
        | assertionFailed => rfl
      have hresult := rc.terminal hres'
      have hq : plannerRunQ g (withResolve current spills dropped) s u := hresult.finish
        (hal.trans hcode) (by cases res <;> exact ctx.count)
      apply Program.Intercept.intro_label (i := 22)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte]
        exact ⟨withResolve current spills dropped, lo', resolveLocals locals hl,
          h1.toBd, h1.ok, hq⟩
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte]
        omega) (by
      intro spills dropped res lo' u hr h1 hres hm0
      have hmodel := hcells.resolved hr scratch
      let rc := ctx.afterResolve hblocked scratch res spills dropped hmodel
      have hnone : ¬ Flat.droppedCount (withResolve current spills dropped).p.m
          (withResolve current spills dropped).dropped > before := by
        change ¬ Flat.droppedCount current.p.m dropped > Flat.droppedCount current.p.m current.dropped
        simp only [hm0, Flat.droppedCount, dropped_end (by decide : ¬ (0 : Word) < 0#64)]
        decide
      apply Program.Intercept.intro_label (i := 32)
      · decide
      left
      refine ⟨h1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte]
        exact ⟨withResolve current spills dropped, before, lo', resolveLocals locals hl,
          rc, hres, hnone, h1.toBd, h1.ok⟩
      · simp only [runV, String.reduceEq, or_false, or_true, ↓reduceIte]
        omega) (by
      intro spills dropped res lo' u hr h1 hres hm0 hbp' hax hcx hdx
      have hmodel := hcells.resolved hr scratch
      let rc := ctx.afterResolve hblocked scratch res spills dropped hmodel
      have htargets := resolve_targetsFrom current.p.fl current.spills current.dropped M
        ctx.out.blockedOffset ctx.out.blockedExcess ⟨ctx.out.dest, ctx.out.pos⟩ ctx.out.size scratch
        hmodel ctx.targets
      have hretry : RetryLI P (withResolve current spills dropped) M F s ra lo'
          (resolveLocals locals hl) u := ⟨h1, htargets⟩
      refine ⟨?_, Or.inl ?_⟩
      · simp only [FullRunInv, RunInv, Names.plannerRun, String.reduceEq, or_false, ↓reduceIte]
        refine ⟨withResolve current spills dropped, M, before, rc, hres,
          lo', resolveLocals locals hl, (0 : Word), hretry, ?_, ?_, hcx, hbp', ?_⟩
        · change 0#64 < current.p.m
          bv_omega
        · exact hax.trans (by change current.p.drp = current.p.drp + 0#64; bv_omega)
        · rw [hdx]
          rfl
      · simp only [runV, String.reduceEq, or_false, ↓reduceIte, hb, hbp', hax, hp,
          BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
        change (g.p.m - before).toNat * 65536 + 4096 + g.p.m.toNat <
          (current.p.m - before).toNat * 65536 + 8000
        rw [hm]
        omega) (by
      intro spills dropped lo' u hlo hmem hr harg
      let rc := ctx.afterResolve hblocked scratch .assertionFailed spills dropped
        (hcells.resolved hr scratch)
      have hresult : RunResult g (withResolve current spills dropped) s .assertionFailed :=
        rc.terminal (by change Flat.Resolution.assertionFailed ≠ .dropped; decide)
      have hq := hresult.exit (t := u) ctx.count
      refine Or.inr ⟨Or.inr ⟨rfl, harg, withResolve current spills dropped,
        hq, withResolve_ok h0.ok spills dropped, fr s lo' (resolveLocals locals hl),
        ra.toBitVec, ?_, hmem⟩, ?_⟩
      · simp [fr, saved, hlo, resolveLocals, hl, plannerRunD]
      · intro l hl heq
        exact False.elim (hout l hl heq))
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ⟨lo, h0.toPostEmitLI⟩ hbp

end
end Bbu.Unit.PlannerRunU
