import BbuKraken.Unit.Defs

/-!
# `buildBottomUp`

`c/bbu/<Names.buildBottomUp>.S`: 6 `pushq` and `subq $24`, so 2068 free words (9, and 2059 for
the call of `permute`). The loop over the target offsets calls `generate`, `swapWith`,
`isSpilled`, `shallowestCopyPosition`, and at the end `permute`.

`loopA` is the state of the constructor for destinations that are distinct and below `n`. The
flat model keeps the invariant of `Model.lean` (`Inv`) on this state, and the invariant gives
the preconditions of the callees (see the callee files). The caller is `build_bottom_up`
(`Unit/Top.lean`), which uses the flat result (`loopQ`).
-/

namespace Bbu.Unit

theorem loop_unit [Host] [FunDecls]
    (hperm : Sep.Spec Names.permute permuteA 2058 permuteQ)
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (hgen : Sep.Spec Names.generate generateA 11 generateQ)
    (hswap : Sep.Spec Names.swapWith swapWithA 0 swapWithQ) :
    UnitThm loopAsm loopA 2068 loopQ := by
  sorry

end Bbu.Unit
