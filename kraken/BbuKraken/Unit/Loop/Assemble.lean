module

public import BbuKraken.Unit.Loop.Head
import all BbuKraken.Unit.Loop.Head
public import BbuKraken.Unit.Loop.Urgent
import all BbuKraken.Unit.Loop.Urgent
public import BbuKraken.Unit.Loop.Gen
import all BbuKraken.Unit.Loop.Gen
public import BbuKraken.Unit.Loop.Bound
import all BbuKraken.Unit.Loop.Bound
public import BbuKraken.Unit.Loop.Swap
import all BbuKraken.Unit.Loop.Swap

@[expose] public section

/-!
# `buildBottomUp`: the unit theorem from the block lemmas

`loop_of_blocks` gives `UnitThm loopAsm loopA 2068 loopQ` from `Program.WP.cfg` with `LInv`
and `V` (`Inv.lean`), and one block lemma for each label of `labels` (parts P2 to P6).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Loop

-- Each block of `loopAsm` has a label in `labels`.
theorem labels_cover : loopAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels]
  cfg_labels

theorem loop_of_blocks [Host] [FunDecls]
    (hperm : ∀ p, Sep.SpecW Names.permute permW (permuteA p) 1034 (permuteQ p))
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (hgen : Sep.Spec Names.generate generateA 11 generateQ)
    (hswap : Sep.Spec Names.swapWith swapWithA 0 swapWithQ) :
    UnitThm loopAsm loopA 2068 loopQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (LInv S g F s ra) (V S) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry S g F s ra
  · exact b_fn S g F s ra hpre
  · exact b_0 S g F s ra hpre
  · exact b_1 S g F s ra hpre hperm
  · exact b_2 S g F s ra hpre
  · exact b_3 S g F s ra hpre
  · exact b_4 S g F s ra hpre
  · exact b_5 S g F s ra hpre hspill hcopy
  · exact b_6 S g F s ra hpre
  · exact b_7 S g F s ra hpre
  · exact b_8 S g F s ra hpre
  · exact b_9 S g F s ra hpre
  · exact b_10 S g F s ra hpre
  · exact b_11 S g F s ra hpre hswap
  · exact b_12 S g F s ra hpre
  · exact b_13 S g F s ra hpre
  · exact b_14 S g F s ra hpre hgen
  · exact b_15 S g F s ra hpre hgen
  · exact b_16 S g F s ra hpre hgen
  · exact b_17 S g F s ra hpre hswap
  · exact b_18 S g F s ra hpre
  · exact b_19 S g F s ra hpre
  · exact b_20 S g F s ra hpre
  · exact b_21 S g F s ra hpre
  · exact b_22 S g F s ra hpre
  · exact b_23 S g F s ra hpre
  · exact b_24 S g F s ra hpre
  · exact b_25 S g F s ra hpre
  · exact b_26 S g F s ra hpre
  · exact b_27 S g F s ra hpre
  · exact b_28 S g F s ra hpre
  · exact b_29 S g F s ra hpre
  · exact b_30 S g F s ra hpre
  · exact b_31 S g F s ra hpre

end Loop
end Bbu.Unit
