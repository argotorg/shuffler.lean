import BbuKraken.Unit.Defs

/-!
# `shallowestCopyPosition`

`c/bbu/<Names.shallowestCopyPosition>.S`: no frame, no call, no store. It compares the low 6
bytes of `m_stack[i]` and of the slot, for `i` from `size - 1` down, and returns `-1` if no slot
is equal.

It reads only the slots below `m_size`, and `m_size ≤ n` (`G.Ok`), so it needs no precondition.
The callers (`produce`, `permute`, `buildBottomUp`) use `g' = g` and the result in `rax`.
-/

namespace Bbu.Unit

theorem shallowestCopy_unit [Host] [FunDecls] :
    UnitThm shallowestCopyAsm shallowestCopyA 0 shallowestCopyQ := by
  sorry

end Bbu.Unit
