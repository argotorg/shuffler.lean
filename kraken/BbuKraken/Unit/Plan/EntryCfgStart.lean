module

public import BbuKraken.Unit.Plan.EntryCfgDefs
import all BbuKraken.Unit.Plan.EntryCfgDefs
public import BbuKraken.Unit.Plan.EntryGuard
import all BbuKraken.Unit.Plan.EntryGuard

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

section
variable [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem cfg_entry : planAsm.ForallBlocks fun blk =>
    blk.label = .entry → EntryObl g F s ra blk := by
  cfg_block [EntryObl]
  intro t ht
  kvcgen64
  simpa only [EntryInv, Names.plan, ↓reduceIte] using ht

set_option maxRecDepth 4096 in
theorem cfg_fn (hp : Pre g F s) (hs : Sizes g) :
    planAsm.ForallBlocks fun blk =>
      blk.label = .label Names.plan → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl, Names.plan]
  intro t ht
  simp only [EntryInv, Names.plan, ↓reduceIte] at ht
  subst t
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label Names.plan) 1 (s.pushRa ra) b j u
  have hh := b_fn g F s ra hp hs (I' (.label ".LB.plan.0") 2) I' (EntryExit g F s ra)
    (by
      intro u hu
      obtain ⟨lo, locals, h, hi, hids⟩ := hu
      apply Program.Intercept.intro_label (i := 2) (by decide)
      left
      refine ⟨h.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simpa only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] using
          (show SourceHead g F s ra u from ⟨lo, locals, h, hi, hids⟩)
      · have hm := sizes_m hs
        change g.r.p.m.toNat ≤ 1024 at hm
        simp only [entryV, Names.plan, String.reduceEq, or_false, ↓reduceIte]
        omega)
    (by
      intro u hu hz
      apply Program.Intercept.intro_label (i := 15) (by decide)
      left
      refine ⟨hu.choose_spec.choose_spec.1.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨hu, hz⟩
      · simp only [entryV, Names.plan, String.reduceEq, or_false, or_true, ↓reduceIte]
        decide)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Names.plan, Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh

end
end Bbu.Unit.EntryValidU
