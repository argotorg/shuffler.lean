module

public import FlatShuffler.Unit.Plan.PlannerRunCfgDefs
import all FlatShuffler.Unit.Plan.PlannerRunCfgDefs

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

set_option experimental.vcgen true

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

set_option maxRecDepth 4096 in
theorem builder_assertion_block [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit")
    (hX : ∀ u, StkMem plannerRunD (plannerCallOwnedMemory P g ∗ F) s u.dmem →
      u.regs.get64 .rdi = 1#64 → E (label "exit") u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.6" →
      ∀ t, (∃ lo locals, Bd P g F s ra lo locals t) → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  cfg_block
  intro t ⟨lo, locals, hb⟩
  have he := ProofKit.external_call_spec "exit" hexit
  kvcgen64 [he]
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => exact (hb.exit_mem 0).1
  | jumpOut =>
    refine Or.inr ⟨hX _ (hb.exit_mem _).2 rfl, ?_⟩
    intro l hl heq
    exact False.elim (hout l hl heq)

set_option maxRecDepth 4096 in
theorem cfg_builder_assert [Host] [FunDecls] (P : Addr) (g : PlannerCallMemory) (F : MProp 64)
    (s : MachineData) (ra : Int64) (resolvePhase : Label → MachineData → Prop)
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ plannerRunAsm.labels, label l ≠ label "exit") :
    plannerRunAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Planner.run.6" → RunObl P g F s ra resolvePhase blk := by
  cfg_view as hv
  cfg_block [RunObl]
  intro t ht
  simp only [RunInv, Names.plannerRun, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨current, M0, hok, ⟨ctx⟩, lo, locals, h0, hi, hb⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    RunInv P g F s ra resolvePhase b u ∧
      Program.Decreases (runV g) (.label ".LB.Planner.run.6") 8 t b j u
  have hh := builder_assertion_block P current F s ra (I' (.label ".LB.Planner.run.7") 9)
    I' (RunExit P g F s ra) hexit hout (by
      intro u hm harg
      let v : MachineData := {u with regs := {u.regs with rax := ⟨2#64⟩}}
      have hq := ctx.mapping_fail (t := v) hok M0 hi hb rfl
      exact Or.inr ⟨rfl, harg, current, plannerRunX_of_Q hq rfl, hok, hm⟩)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ⟨lo, locals, h0.toBd⟩

end FlatShuffler.Unit.PlannerRunU
