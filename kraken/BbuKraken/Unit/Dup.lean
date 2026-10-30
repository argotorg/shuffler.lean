import BbuKraken.Unit.Defs

/-!
# `dup`

`c/bbu/<Names.dup>.S`: no frame, no call. If the slot at `copy` is not a return label, it stores
the operation to record `traceSize`, copies `m_stack[copy]` to `m_stack[size]`, increments the
two counters, and then binds the new slot to the destination if `m_positionOf[destination]` is
`-1`.

The caller is `produce`. The copy is a result of `shallowestCopyPosition` that is not `-1`, so it
is below `size ≤ n`; the destination is `t < n`; `produceA` gives `len < n` and `nops < 6n`
(`dupA`). `produce` uses the flat result (`dupQ`).
-/

namespace Bbu.Unit

theorem dup_unit [Host] [FunDecls] : UnitThm dupAsm dupA 0 dupQ := by
  sorry

end Bbu.Unit
