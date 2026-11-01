module

public import BbuKraken.Unit.Plan.EntryCfgDefs
import all BbuKraken.Unit.Plan.EntryCfgDefs
public import BbuKraken.Unit.Plan.EntryTail
import all BbuKraken.Unit.Plan.EntryTail
public import BbuKraken.Unit.Plan.EntryLocalOutput
import all BbuKraken.Unit.Plan.EntryLocalOutput

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

section
variable [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxRecDepth 8192 in
theorem cfg_8 (hp : Pre g F s) (hs : Sizes g) (hrun : PlannerRunSpec) :
    planAsm.ForallBlocks fun blk => blk.label = .label ".LB.plan.8" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hsrc, htgt, ht⟩ := ht
  obtain ⟨hok, hdi, hsi, hdx, hcx, h8, h9, ha, hcp, hc0, htr, hmem⟩ := hp
  let cg := withDropped g (wanted g)
  have hcok : cg.Ok := ⟨hok.sw, hok.tw, hok.ids, hok.ops, hok.traceLength⟩
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.8") 10 t b j u
  have hh := b_8_call cg F s ra
    (checked_run_ok cg hcok hs hsrc htgt) hcok hcp hc0 htr ha hs hrun
    (I' (.label ".LB.plan.9") 11) I' (EntryExit g F s ra) (by
      intro r u lo l hb hrok hq
      apply entry_tail cg (withRun cg r) F s u ra lo (l.toList (withRun cg r).r) hb hq
      · intro v hv hqv hal
        have hran := ran_of_runQ g (withRun cg r) s v hok hs hsrc htgt ha htr hqv rfl
        apply Program.Intercept.intro_label (i := 12)
        · decide
        left
        refine ⟨hv.kb.stack (by decide), ?_, Or.inl ?_⟩
        · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
          exact ⟨withRun cg r, lo, l, hv, hrok, result_blocked hran hal⟩
        · simp [entryV]
      · intro v hv hqv h1 h2
        have hran := ran_of_runQ g (withRun cg r) s v hok hs hsrc htgt ha htr hqv rfl
        apply Program.Intercept.intro_label (i := 11)
        · decide
        left
        refine ⟨hv.kb.stack (by decide), ?_, Or.inl ?_⟩
        · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
          exact ⟨withRun cg r, lo, l, hv, hrok, result_done hran h1 h2⟩
        · simp [entryV]
      · intro v hv hqv h2 hdx
        have hran := ran_of_runQ g (withRun cg r) s v hok hs hsrc htgt ha htr hqv rfl
        refine ⟨?_, Or.inl ?_⟩
        · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
          exact ⟨withRun cg r, lo, l.toList (withRun cg r).r, hv, hrok,
            hdx ▸ result_failed hran h2⟩
        · simp [entryV])
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh t ht

set_option maxRecDepth 8192 in
theorem cfg_9 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.9" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', lo, locals, hb, hok, hres⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.9") 11 t b j u
  have hh := b_9 g' F s t ra (Post g F s)
    (I' (.label ".LB.plan.10") 12) I' (by
      intro lo' locals' u hb' hm hax
      refine ⟨g', hok, ?_, hm⟩
      change ResultWord g g' (rax u)
      rw [hax]
      exact hres)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ⟨lo, locals, hb⟩

set_option maxRecDepth 8192 in
theorem cfg_10 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.10" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', lo, l, hb, hok, hres⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.10") 12 t b j u
  have hh := b_10 g' F s t ra lo (l.toList g'.r) hb hb.callSaw hb.callCount
    (I' (.label ".LB.plan.11") 13) I' (EntryExit g F s ra) (by
      intro u hu hdx
      apply Program.Intercept.intro_label (i := 10)
      · decide
      left
      refine ⟨hu.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨withSawOut g' g'.r.p.saw, lo, l.toList g'.r, hu, ⟨hok.sw, hok.tw, hok.ids, hok.ops, hok.traceLength⟩, hdx ▸ hres⟩
      · simp [entryV])
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh

set_option maxRecDepth 8192 in
theorem cfg_11 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.11" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', lo, l, hb, hok, hres⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.11") 13 t b j u
  have hh := b_11 g' F s t ra lo (l.toList g'.r) hb hb.callSaw
    (I' (.label ".LB.plan.12") 14) I' (EntryExit g F s ra) (by
      intro u hu hdx
      apply Program.Intercept.intro_label (i := 10)
      · decide
      left
      refine ⟨hu.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨withSawOut g' g'.r.p.saw, lo, l.toList g'.r, hu, ⟨hok.sw, hok.tw, hok.ids, hok.ops, hok.traceLength⟩, hdx ▸ hres⟩
      · simp [entryV])
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh

end
end Bbu.Unit.EntryValidU
