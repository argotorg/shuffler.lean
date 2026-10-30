import BbuKraken.Unit.Permute.Assemble
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
`Permute.permute_of_b73` (`Permute/Assemble.lean`) does the assembly; `Permute.b_73`
(`Permute/D3.lean`) is the lemma of `.LB73`.
-/

namespace Bbu.Unit

theorem permute_unit [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    UnitThm finishAsm permuteA 2058 permuteQ :=
  Permute.permute_of_b73 hcopy Permute.b_73

end Bbu.Unit
