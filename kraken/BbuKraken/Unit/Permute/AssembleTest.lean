module

public import BbuKraken.Unit.Permute.Assemble
import all BbuKraken.Unit.Permute.Assemble

@[expose] public section

/-! # Tests: `labels_cover` and `permute_of_b22` -/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.Permute.AssembleTest
open Bbu.Unit.Permute

-- `labels` has 28 labels and no label two times (one for each block of `finishAsm`).
example : labels.length = 28 := rfl
example : labels.Nodup := by decide

-- The cover of `Assemble.lean`.
example : finishAsm.ForallBlocks fun blk => blk.label ∈ labels := labels_cover

-- A list without the last label (`.LB.Emission.permute.24`) does not cover the blocks: the steps of
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

-- A list without `.LB.Emission.permute.22` (the block of `h22`): the cover is false.
example : ¬ Program.ForallBlocks finishAsm fun blk => blk.label ∈ labels.erase (.label ".LB.Emission.permute.22") := by
  intro h
  have hf : Program.ForallBlocks finishAsm fun _ => False := by
    cfg_view as hview
    rw [Program.ForallBlocks, hview] at h
    simp [Program.forallBlocksFrom, labels] at h
  exact hf.entry

-- The unit theorem from `hcopy` and an obligation for `.LB.Emission.permute.22`. The lemma of another block
-- (`.LB.Emission.permute.24`) does not take the place of `h22`.
example [Host] [FunDecls] (p0 : Vector Word MAX_N)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (h22 : ∀ S g p0 F s ra, Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s →
      Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.22" →
        Obl S g p0 F s ra blk) :
    UnitThmW finishAsm permW (permuteA p0) 1034 (permuteQ p0) := by
  fail_if_success (exact permute_of_b22 p0 hcopy fun S g p F s ra hpre => b_24 S g p F s ra hpre)
  exact permute_of_b22 p0 hcopy h22

-- The lemma of `.LB.Emission.permute.24` has the shape of `h22` with its own label. Thus the failure above is
-- only from the label.
example [Host] [FunDecls] : ∀ S g p0 F s ra, Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s →
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.24" →
      Obl S g p0 F s ra blk :=
  fun S g p0 F s ra hpre => b_24 S g p0 F s ra hpre

end Bbu.Unit.Permute.AssembleTest
