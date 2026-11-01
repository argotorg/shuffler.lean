module

public import BbuKraken.Unit.Permute.A
import all BbuKraken.Unit.Permute.A
public import BbuKraken.Unit.Permute.C1
import all BbuKraken.Unit.Permute.C1
public import BbuKraken.Unit.Permute.C2
import all BbuKraken.Unit.Permute.C2
public import BbuKraken.Unit.Permute.D1
import all BbuKraken.Unit.Permute.D1
public import BbuKraken.Unit.Permute.D2
import all BbuKraken.Unit.Permute.D2

@[expose] public section

/-!
# `permute`: the unit theorem from the block lemmas

`permute_of_b22 p0` gives `UnitThmW finishAsm permW (permuteA p0) 1034 (permuteQ p0)` from
`Program.WP.cfg` with `LInv` and `V`, and one block lemma for each label of `labels`. The
obligation of `.LB.Emission.permute.22` is the hypothesis `h22` (it has the type of `b_22`).
Thus `permute_unit hcopy p0` is `Permute.permute_of_b22 p0 hcopy Permute.b_22`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

-- Each block of `finishAsm` has a label in `labels`.
theorem labels_cover : finishAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels]
  pm_labels

theorem permute_of_b22 [Host] [FunDecls] (p0 : Vector Word MAX_N)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (h22 : ∀ S g p0 F s ra, Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s →
      Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.22" →
        Obl S g p0 F s ra blk) :
    UnitThmW finishAsm permW (permuteA p0) 1034 (permuteQ p0) := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (LInv S g p0 F s ra) (V s g) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry S g p0 F s ra
  · exact b_fn S g p0 F s ra hpre
  · exact b_0 S g p0 F s ra hpre
  · exact b_1 S g p0 F s ra hpre
  · exact b_2 S g p0 F s ra hpre
  · exact b_3 S g p0 F s ra hpre
  · exact b_4 S g p0 F s ra hpre
  · exact b_5 S g p0 F s ra hpre
  · exact b_6 S g p0 F s ra
  · exact b_7 S g p0 F s ra hpre
  · exact b_8 S g p0 F s ra hpre
  · exact b_9 S g p0 F s ra hpre
  · exact b_10 S g p0 F s ra hpre
  · exact b_11 S g p0 F s ra hpre
  · exact b_12 S g p0 F s ra hpre hcopy
  · exact b_13 S g p0 F s ra hpre
  · exact b_14 S g p0 F s ra hpre
  · exact b_15 S g p0 F s ra hpre
  · exact b_16 S g p0 F s ra hpre
  · exact b_17 S g p0 F s ra hpre
  · exact b_18 S g p0 F s ra hpre
  · exact b_19 S g p0 F s ra hpre
  · exact b_20 S g p0 F s ra hpre
  · exact b_21 S g p0 F s ra hpre
  · exact h22 S g p0 F s ra hpre
  · exact b_23 S g p0 F s ra hpre
  · exact b_24 S g p0 F s ra hpre
  · exact b_25 S g p0 F s ra

end Permute
end Bbu.Unit
