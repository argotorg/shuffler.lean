import BbuKraken.Unit.Permute.A
import BbuKraken.Unit.Permute.C1
import BbuKraken.Unit.Permute.C2
import BbuKraken.Unit.Permute.D1
import BbuKraken.Unit.Permute.D2
import BbuKraken.Unit.Permute.D3

/-!
# `permute`

`c/bbu/<Names.permute>.S`: 6 `pushq` and `subq $16408` (the arrays `permutation` and
`desiredBy`), so 2058 free words (2057 and one for the call of `shallowestCopyPosition`).
It regroups equal slots and then sorts the stack by the destinations with swaps.

`PermOk` gives that the destinations are a permutation of the offsets below `size`: the loop
ends after at most `2 * size - 1` steps with at most one swap each, so the trace has room
(`nops + 2 * len ≤ 6n`), and the stores to `m_positionOf` are below `size`. The caller is
`buildBottomUp` when no generation is pending: `Inv.finish` gives `IsPerm` and
`trace + 2 * len ≤ 6n`.

The proof is `Program.WP.cfg` with the invariant `Permute.LInv` and the variant `Permute.V`
(`Permute/Inv.lean`), and one lemma for each block (`Permute/A.lean` to `Permute/D3.lean`).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit
open Permute

theorem permute_unit [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    UnitThm finishAsm permuteA 2058 permuteQ := by
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  refine Program.WP.cfg (LInv S g F s ra) (V s g)
    (forallBlocks_cases (P := Obl S g F s ra) labels (by simp only [labels]; pm_labels) ?_) rfl
  simp only [labels, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨b_entry S g F s ra, b_fn S g F s ra hpre, b_57 S g F s ra hpre, b_54 S g F s ra,
    b_56 S g F s ra hpre, b_58 S g F s ra hpre, b_61 S g F s ra hpre, b_62 S g F s ra hpre,
    b_95 S g F s ra hpre, b_64 S g F s ra hpre, b_65 S g F s ra hpre, b_66 S g F s ra hpre,
    b_68 S g F s ra hpre, b_63 S g F s ra hpre, b_70 S g F s ra hpre, b_60 S g F s ra hpre,
    b_71 S g F s ra hpre hcopy, b_96 S g F s ra hpre, b_86 S g F s ra hpre,
    b_72 S g F s ra hpre, b_97 S g F s ra hpre, b_74 S g F s ra hpre, b_98 S g F s ra hpre,
    b_78 S g F s ra hpre, b_80 S g F s ra hpre, b_84 S g F s ra hpre, b_73 S g F s ra hpre,
    b_82 S g F s ra hpre, b_99 S g F s ra hpre⟩

end Bbu.Unit
