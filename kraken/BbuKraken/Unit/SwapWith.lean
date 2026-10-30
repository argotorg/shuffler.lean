import BbuKraken.Unit.Defs

/-!
# `swapWith`

`c/bbu/<Names.swapWith>.S`: no frame, no call. It asserts `pos < size`, that `pos` is not
final, and `1 ≤ depth ≤ 16`. Then it swaps the two slots (the top slot gets the 6 low bytes of
the other slot), stores the operation, swaps the two destinations, and writes `m_positionOf` at
each destination that is not `-1`.

`DestOk` gives that each such destination is below `n ≤ MAX_N`, so the stores to `m_positionOf`
are in the view. The callers are `generate` (`nops + 1 < 6n` after `produce`, and `produce`
binds the new slot to `t < n`) and `buildBottomUp` (`Inv.lt` and `Inv.pos`). They use the flat
result (`swapWithQ`).
-/

namespace Bbu.Unit

theorem swapWith_unit [Host] [FunDecls] : UnitThm swapWithAsm swapWithA 0 swapWithQ := by
  sorry

end Bbu.Unit
