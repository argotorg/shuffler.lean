import BbuKraken.Unit.Defs

/-!
# `generate`

`c/bbu/<Names.generate>.S`: 2 `pushq`, so 11 free words (2, and 9 for the call of `produce`).
It asserts `t < n`, calls `produce`, and then, if `t + 1 < size` and `t` is not final, swaps the
destinations of `t` and of the top slot (equal slots) or calls `swapWith(t)`.

The preconditions of the callees: `produceA` from the check `t < n` and `generateA`; after
`produce` the trace has one more record (`nops + 1 < 6n`) and the new slot is bound to `t < n`
(`DestOk`, `swapWithA`). The caller is `buildBottomUp`: `Inv.lt` gives `len < n` and
`nops + 3 ≤ 6n`, and `Inv.pos` gives `DestOk`.
-/

namespace Bbu.Unit

theorem generate_unit [Host] [FunDecls]
    (hprod : Sep.Spec Names.produce produceA 8 produceQ)
    (hswap : Sep.Spec Names.swapWith swapWithA 0 swapWithQ) :
    UnitThm generateAsm generateA 11 generateQ := by
  sorry

end Bbu.Unit
