import BbuKraken.Unit.Defs

/-!
# `push`

`c/bbu/<Names.push>.S`: no frame, no call. It stores the slot word to `m_stack[size]` and the
operation to record `traceSize`, increments the two counters, and then binds the new slot to
the destination if `m_positionOf[destination]` is `-1`.

The caller is `produce`, with the destination `t` and `len < n`, `nops < 6n` (`produceA`), so
the stores are in the view (`pushA`). `produce` uses the flat result (`pushQ`).
-/

namespace Bbu.Unit

theorem push_unit [Host] [FunDecls] : UnitThm pushAsm pushA 0 pushQ := by
  sorry

end Bbu.Unit
