import BbuKraken.Unit.Permute.Assemble
import BbuKraken.Unit.Permute.D3

/-!
# `permute`

`c/bbu/<Names.permute>.S`: 6 `pushq` and `subq $8216` (the array `desiredBy` and two
words), so 1034 free words (1033 and one for the call of `shallowestCopyPosition`). The array
`permutation` is the argument `rsi`: the function owns `permW s`.
It regroups equal slots and then sorts the stack by the destinations with swaps.

The theorem holds for each ghost `p0`. `permuteA p0` gives that `p0` is a bijection of the
offsets below `size` and that `permutation` holds `p0`: the loop ends after at most
`2 * size - 1` steps with at most one swap each, so the trace has room
(`nops + 2 * len ≤ 6n`). `DestOk` gives that each destination is `NONE` or below the target
size; the code stores to `m_positionOf` only for a destination that is not `NONE`. The caller is
`buildBottomUp` when no generation is pending.

The proof is `Program.WP.cfg` with the invariant `Permute.LInv` and the variant `Permute.V`
(`Permute/Inv.lean`), and one lemma for each block (`Permute/A.lean` to `Permute/D3.lean`).
`Permute.permute_of_b22` (`Permute/Assemble.lean`) does the assembly; `Permute.b_22`
(`Permute/D3.lean`) is the lemma of `.LB.Emission.permute.22`.
-/

namespace Bbu.Unit

theorem permute_unit [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ) :
    ∀ p0, UnitThmW finishAsm permW (permuteA p0) 1034 (permuteQ p0) :=
  fun p0 => Permute.permute_of_b22 p0 hcopy Permute.b_22

end Bbu.Unit
