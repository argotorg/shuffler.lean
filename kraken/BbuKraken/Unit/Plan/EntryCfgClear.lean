module

public import BbuKraken.Unit.Plan.EntryCfgDefs
import all BbuKraken.Unit.Plan.EntryCfgDefs
public import BbuKraken.Unit.Plan.EntryClear
import all BbuKraken.Unit.Plan.EntryClear

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

private theorem clear_gap (p m i : Word) (hi : i < m) :
    0 < (p + m - (p + i)).toNat := by bv_omega

private theorem clear_gap_bound (p m i : Word) (hi : i < m) (hm : m.toNat ≤ 1024) :
    (p + m - (p + i)).toNat ≤ 1024 := by bv_omega

private theorem clear_gap_step (x y : Word) (h : 0 < (y - x).toNat) :
    (y - (1#64 + x)).toNat < (y - x).toNat := by bv_omega

section
variable [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxRecDepth 8192 in
theorem cfg_6 (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.6" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨ht, hm⟩ := ht
  have hsrc := ht.choose_spec.choose_spec.2.1
  have htgt := ht.choose_spec.choose_spec.2.2
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.6") 8 t b j u
  have hh := b_6 g F s t ra hm (I' (.label ".LB.plan.7") 9) I' (EntryExit g F s ra) (by
    intro u hu
    obtain ⟨lo, locals, i, hc, hi, hax, h9, hmodel⟩ := hu
    have hu : ClearHead g F s ra (wanted g) u := ⟨lo, locals, i, hc, hi, hax, h9, hmodel⟩
    have hmN := sizes_m hs
    simp only [MAX_N] at hmN
    have hgap : (r9 u - rax u).toNat ≤ 1024 := by
      rw [hax, h9]
      exact clear_gap_bound _ _ _ hi hmN
    refine ⟨?_, Or.inl ?_⟩
    · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨hsrc, htgt, g.r.dropped, ?_⟩
      exact hu
    · simp only [entryV, String.reduceEq, ↓reduceIte, or_self]
      omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

set_option maxRecDepth 8192 in
theorem cfg_7 (hs : Sizes g) : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.7" → EntryObl g F s ra blk := by
  cfg_view as hv
  cfg_block [EntryObl]
  intro t ht
  simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hsrc, htgt, d, ht⟩ := ht
  obtain ⟨lo, locals, i, hc, hi, hax, h9, hmodel⟩ := ht
  have ht : ClearHead (withDropped g d) F s ra (wanted g) t :=
    ⟨lo, locals, i, hc, hi, hax, h9, hmodel⟩
  have hgap : 0 < (r9 t - rax t).toNat := by
    rw [hax, h9]
    exact clear_gap _ _ _ hi
  let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
    EntryInv g F s ra b u ∧
      Program.Decreases (entryV g) (.label ".LB.plan.7") 9 t b j u
  have hh := b_7 (withDropped g d) F s t ra hs (wanted g)
    (I' (.label ".LB.plan.8") 10) I' (EntryExit g F s ra) (by
      intro d' u hu hau
      obtain ⟨lo', locals', j, hc', hj, hax', h9', hmodel'⟩ := hu
      have hu : ClearHead (withDropped g d') F s ra (wanted g) u :=
        ⟨lo', locals', j, hc', hj, hax', h9', hmodel'⟩
      have hnine : r9 u = r9 t := h9'.trans h9.symm
      apply Program.Intercept.intro_label (i := 8)
      · decide
      left
      refine ⟨hc'.kb.stack (by decide), ?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨hsrc, htgt, d', hu⟩
      · simp only [entryV, String.reduceEq, or_self, ↓reduceIte, hnine, hau]
        have hdec := clear_gap_step _ _ hgap
        omega) (by
      intro d' u hu hd'
      refine ⟨?_, Or.inl ?_⟩
      · simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte]
        exact ⟨hsrc, htgt, hd' ▸ hu⟩
      · simp only [entryV, String.reduceEq, or_self, ↓reduceIte]
        omega)
  rw [Program.ForallBlocks, hv] at hh
  simp only [Program.forallBlocksFrom, CfgLabel.label.injEq, reduceCtorEq,
    String.reduceEq, false_implies, true_implies, and_true, true_and] at hh
  exact hh ht

end
end Bbu.Unit.EntryValidU
