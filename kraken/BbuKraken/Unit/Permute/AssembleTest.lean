import BbuKraken.Unit.Permute.Assemble

/-! # Tests: `labels_cover` and `permute_of_b73` -/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.Permute.AssembleTest
open Bbu.Unit.Permute

-- `labels` has 29 labels and no label two times (one for each block of `finishAsm`).
example : labels.length = 29 := rfl
example : labels.Nodup := by decide

-- The cover of `Assemble.lean`.
example : finishAsm.ForallBlocks fun blk => blk.label ∈ labels := labels_cover

-- A list without the last label (`.LB99`) does not cover the blocks: the steps of
-- `labels_cover` fail.
example : (Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.dropLast) ∨ True := by
  fail_if_success
    (left; simp only [labels, List.dropLast_cons₂, List.dropLast_singleton]; pm_labels; done)
  exact Or.inr trivial

-- The same list: the cover is false. Thus no proof of it is possible, and the failure above is
-- not only a failure of the tactic. `cfg_view` needs a goal `Program.ForallBlocks p P`: `hf` is
-- that goal, and it closes only when `simp` makes `h` false.
example : ¬ Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.dropLast := by
  intro h
  have hf : Program.ForallBlocks finishAsm fun _ => False := by
    cfg_view as hview
    rw [Program.ForallBlocks, hview] at h
    simp [Program.forallBlocksFrom, labels] at h
  exact hf.entry

-- A list without the first label (`.entry`): the cover is false.
example : ¬ Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.tail := by
  intro h
  have hf : Program.ForallBlocks finishAsm fun _ => False := by
    cfg_view as hview
    rw [Program.ForallBlocks, hview] at h
    simp [Program.forallBlocksFrom, labels] at h
  exact hf.entry

-- A list without `.LB73` (the block of `h73`): the cover is false.
example : ¬ Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.erase (.label ".LB73") := by
  intro h
  have hf : Program.ForallBlocks finishAsm fun _ => False := by
    cfg_view as hview
    rw [Program.ForallBlocks, hview] at h
    simp [Program.forallBlocksFrom, labels] at h
  exact hf.entry

-- The unit theorem from `hcopy` and an obligation for `.LB73`. The lemma of another block
-- (`.LB99`) does not take the place of `h73`.
example [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (h73 : ∀ S g F s ra, Sep.Pre S g F permuteA 2058 s →
      Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB73" →
        Obl S g F s ra blk) :
    UnitThm finishAsm permuteA 2058 permuteQ := by
  fail_if_success (exact permute_of_b73 hcopy fun S g F s ra hpre => b_99 S g F s ra hpre)
  exact permute_of_b73 hcopy h73

-- The lemma of `.LB99` has the shape of `h73` with its own label. Thus the failure above is
-- only from the label.
example [Host] [FunDecls] : ∀ S g F s ra, Sep.Pre S g F permuteA 2058 s →
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB99" →
      Obl S g F s ra blk :=
  fun S g F s ra hpre => b_99 S g F s ra hpre

end Bbu.Unit.Permute.AssembleTest
