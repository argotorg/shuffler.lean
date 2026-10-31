import BbuKraken.Unit.Plan.EntryCfgDefs
import BbuKraken.Unit.Plan.EntryAdvance
import BbuKraken.Unit.Plan.EntrySource
import BbuKraken.Unit.Plan.EntryTargetStart
import BbuKraken.Unit.Plan.EntryTarget

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

private theorem ready_zero {g : EG} {F : MProp 64} {s t : MachineData} {ra : Int64}
    (hm : g.r.p.m = 0#64) (h : Checked g F s ra t) :
    Ready (withDropped g (wanted g)) F s ra t := by
  have hz : wanted g = g.r.dropped := by
    unfold wanted
    rw [Flat.zeroFrom]
    split
    · rename_i hlt
      rw [hm] at hlt
      exact False.elim (BitVec.lt_irrefl _ hlt)
    · rfl
  rw [hz]
  change Ready g F s ra t
  obtain ⟨lo, locals, hc, _, _⟩ := h
  exact ⟨lo, locals, hc.toClearLI⟩

section
variable [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxRecDepth 4096 in
theorem cfg_0 (hok : g.Ok) (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.0" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  have hi := ht.choose_spec.choose_spec.2.1
  have hm : g.r.p.m ≠ 0#64 := by
    intro he
    rw [he] at hi
    exact BitVec.not_lt_zero hi
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.0") 2 t b j u
  have hh := b_0 g F s t ra hok hs (I' (.label ".LB.plan.1") 3) I'
    (EntryExit g F s ra) (by
      intro u hu hau
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · have hui := hu.choose_spec.choose_spec.2.1
        have hiN : (rax t).toNat < 1024 :=
          Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) (sizes_m hs)
        have hsucc : (rax u).toNat = (rax t).toNat + 1 := by rw [hau]; bv_omega
        simp only [entryV, String.reduceEq, or_false, ↓reduceIte, hsucc]
        change (rax t).toNat < g.r.p.m.toNat at hi
        change (rax u).toNat < g.r.p.m.toNat at hui
        omega) (by
      intro u hu
      apply Program.Intercept.intro_label (i := 3) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using
          (show SourceDone g F s ra u ∧ g.r.p.m ≠ 0#64 from ⟨hu, hm⟩)
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_1 (hok : g.Ok) (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.1" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.1") 3 t b j u
  have hh := b_1 g F s t ra hok (I' (.label ".LB.plan.2") 4) I'
    (EntryExit g F s ra) (by
      intro u hu ha
      apply Program.Intercept.intro_label (i := 1) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte, ha]
        omega) (by
      intro u lo locals hb hbad hdx
      apply Program.Intercept.intro_label (i := 10) (by decide)
      left
      refine ⟨hb.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte, ReturnPhase]
        refine ⟨g, lo, locals, hb, hok, ?_⟩
        rw [hdx]
        exact result_rejected g (-2#64) (model_reject_source g hok hs hbad)
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_2 (hok : g.Ok) (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.2" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨ht, hm⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.2") 4 t b j u
  have hh := b_2 g F s t ra hok hm (I' (.label ".LB.plan.3") 5) I'
    (EntryExit g F s ra) (by
      intro u hu
      apply Program.Intercept.intro_label (i := 5) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · have hn : g.r.p.n.toNat ≤ 1024 := sizes_n hs
        simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        omega) (by
      intro u hu hnm
      apply Program.Intercept.intro_label (i := 7) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using
          (show Checked g F s ra u ∧ g.r.p.m ≠ 0#64 from ⟨hu, hnm⟩)
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        decide)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_3 (hok : g.Ok) (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.3" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  have hi := ht.choose_spec.choose_spec.2.1
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.3") 5 t b j u
  have hh := b_3 g F s t ra hok hs (I' (.label ".LB.plan.4") 6) I'
    (EntryExit g F s ra) (by
      intro u hu hau
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · have hui := hu.choose_spec.choose_spec.2.1
        have hiN : (rax t).toNat < 1024 :=
          Nat.lt_of_lt_of_le (BitVec.lt_def.mp hi) (sizes_n hs)
        have hsucc : (rax u).toNat = (rax t).toNat + 1 := by rw [hau]; bv_omega
        simp only [entryV, String.reduceEq, or_false, ↓reduceIte, hsucc]
        change (rax t).toNat < g.r.p.n.toNat at hi
        change (rax u).toNat < g.r.p.n.toNat at hui
        omega) (by
      intro u hu
      apply Program.Intercept.intro_label (i := 6) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_4 (hok : g.Ok) (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.4" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.4") 6 t b j u
  have hh := b_4 g F s t ra hok (I' (.label ".LB.plan.5") 7) I'
    (EntryExit g F s ra) (by
      intro u hu ha
      apply Program.Intercept.intro_label (i := 4) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte, ha]
        omega) (by
      intro u lo locals hb hsrc hbad hdx
      apply Program.Intercept.intro_label (i := 10) (by decide)
      left
      refine ⟨hb.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte, ReturnPhase]
        refine ⟨g, lo, locals, hb, hok, ?_⟩
        rw [hdx]
        exact result_rejected g (-2#64) (model_reject_target g hok hs hsrc hbad)
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_5 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.5" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.5") 7 t b j u
  have hh := b_5 g F s t ra (I' (.label ".LB.plan.6") 8) I'
    (EntryExit g F s ra) (by
      intro u hu hm
      apply Program.Intercept.intro_label (i := 9) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨hu.choose_spec.choose_spec.2.1, hu.choose_spec.choose_spec.2.2,
          ready_zero hm hu⟩
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        decide) (by
      intro u hu hm
      refine ⟨?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using
          (show Checked g F s ra u ∧ g.r.p.m ≠ 0#64 from ⟨hu, hm⟩)
      · simp only [entryV, String.reduceEq, or_false, ↓reduceIte]
        decide)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 4096 in
theorem cfg_14 (hok : g.Ok) (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.14" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨ht, hm⟩ := ht
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.14") 16 t b j u
  have hh := b_14 g F s t ra hok hm (fun _ u => EntryInv g F s ra .exit u) I'
    (EntryExit g F s ra) (by
      intro u hu
      apply Program.Intercept.intro_label (i := 5) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using hu
      · have hn : g.r.p.n.toNat ≤ 1024 := sizes_n hs
        simp only [entryV, String.reduceEq, or_false, or_true, ↓reduceIte]
        omega) (by
      intro u hu hzm
      apply Program.Intercept.intro_label (i := 9) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨hu.choose_spec.choose_spec.2.1, hu.choose_spec.choose_spec.2.2,
          ready_zero hzm hu⟩
      · simp only [entryV, String.reduceEq, or_false, or_true, ↓reduceIte]
        decide)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, true_and] at hh
  exact hh ht

end
end Bbu.Unit.EntryValidU
