import BbuKraken.Unit.Loop.Assemble

/-!
# `buildBottomUp`

`c/bbu/<Names.buildBottomUp>.S`: 6 `pushq` and `subq $8216`, so 2068 free words (1033, and 1035
for the call of `permute`). The local array at `16(%rsp)` is the argument `permutation` of
`permute` (`permW`). The loop over the target offsets calls `generate`, `swapWith`,
`isSpilled`, `shallowestCopyPosition`, and at the end `permute`.

`loopA` is the loop invariant `HInv` (`Unit/LoopInv.lean`) at `T = 0`, with the room `xo` of the
trace buffer. The caller sets up the state of the constructor, which satisfies it (`HInv.ctor`).
The flat model keeps the invariant of `Model.lean` (`Inv`) on this state, and the invariant gives
the preconditions of the callees (see the callee files). The caller is `build_bottom_up`
(`Unit/Top.lean`), which uses the flat result (`loopQ`).
-/

namespace Bbu.Unit

theorem loop_unit [Host] [FunDecls]
    (hperm : ∀ p, Sep.SpecW Names.permute permW (permuteA p) 1034 (permuteQ p))
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (hgen : Sep.Spec Names.generate generateA 11 generateQ)
    (hswap : Sep.Spec Names.swapWith swapWithA 0 swapWithQ) :
    UnitThm loopAsm loopA 2068 loopQ := by
  exact Loop.loop_of_blocks hperm hspill hcopy hgen hswap

end Bbu.Unit
