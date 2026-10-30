import BbuKraken.Unit.Permute.A
import BbuKraken.Unit.Permute.C1
import BbuKraken.Unit.Permute.C2
import BbuKraken.Unit.Permute.D1
import BbuKraken.Unit.Permute.D2

/-!
# `permute`: the unit theorem from the block lemmas

`permute_of_b73` gives `UnitThm finishAsm permuteA 2058 permuteQ` from `Program.WP.cfg` with
`LInv` and `V`, and one block lemma for each label of `labels`. The obligation of `.LB73` is the
hypothesis `h73` (it has the type of `b_73`). Thus `permute_unit` is
`Permute.permute_of_b73 hcopy Permute.b_73`.
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

theorem permute_of_b73 [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (h73 : ∀ S g F s ra, Sep.Pre S g F permuteA 2058 s →
      Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB73" →
        Obl S g F s ra blk) :
    UnitThm finishAsm permuteA 2058 permuteQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (LInv S g F s ra) (V s g) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl
  · exact b_entry S g F s ra
  · exact b_fn S g F s ra hpre
  · exact b_57 S g F s ra hpre
  · exact b_54 S g F s ra
  · exact b_56 S g F s ra hpre
  · exact b_58 S g F s ra hpre
  · exact b_61 S g F s ra hpre
  · exact b_62 S g F s ra hpre
  · exact b_95 S g F s ra hpre
  · exact b_64 S g F s ra hpre
  · exact b_65 S g F s ra hpre
  · exact b_66 S g F s ra hpre
  · exact b_68 S g F s ra hpre
  · exact b_63 S g F s ra hpre
  · exact b_70 S g F s ra hpre
  · exact b_60 S g F s ra hpre
  · exact b_71 S g F s ra hpre hcopy
  · exact b_96 S g F s ra hpre
  · exact b_86 S g F s ra hpre
  · exact b_72 S g F s ra hpre
  · exact b_97 S g F s ra hpre
  · exact b_74 S g F s ra hpre
  · exact b_98 S g F s ra hpre
  · exact b_78 S g F s ra hpre
  · exact b_80 S g F s ra hpre
  · exact b_84 S g F s ra hpre
  · exact h73 S g F s ra hpre
  · exact b_82 S g F s ra hpre
  · exact b_99 S g F s ra hpre

end Permute
end Bbu.Unit
