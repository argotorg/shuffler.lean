module

public import BbuKraken.Unit.Lowest.Call
import all BbuKraken.Unit.Lowest.Call

@[expose] public section

/-!
# `permuteAtLowestHeight`: the unit theorem from the block lemmas

`lowest_of_blocks` gives `LowestThm permuteAtLowestHeightAsm` from `Program.WP.cfg` with `LInv`
and `V` (`Inv.lean`), and one block lemma for each label of `labels`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Lowest

-- Each block of `permuteAtLowestHeightAsm` has a label in `labels`.
theorem labels_cover : permuteAtLowestHeightAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels]
  cfg_labels

theorem lowest_of_blocks [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels permuteAtLowestHeightAsm, label l ≠ label "exit")
    (hperm : ∀ p, Sep.SpecWWithExit Names.permute permW (permuteA p) 1034
      (permuteQ p) (permuteX p)) :
    LowestThm permuteAtLowestHeightAsm := by
  intro S PM planned g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (LInv S PM planned g F s ra) V ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry S PM planned g F s ra
  · exact b_fn S PM planned g F s ra hpre
  · exact b_0 S PM planned g F s ra hexit hout hpre
  · exact b_head S PM planned g F s ra hpre
  · exact b_1 S PM planned g F s ra hpre
  · exact b_2 S PM planned g F s ra hpre
  · exact b_3 S PM planned g F s ra hpre
  · exact b_4 S PM planned g F s ra hpre hout hperm
  · exact b_fail S PM planned g F s ra _ (Or.inl rfl) hexit hout hpre
  · exact b_fail S PM planned g F s ra _ (Or.inr rfl) hexit hout hpre
  · exact b_7 S PM planned g F s ra hpre
  · exact b_8 S PM planned g F s ra hpre

end Lowest
end Bbu.Unit
