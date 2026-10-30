import BbuKraken.Unit.Defs

/-!
# `isSpilled`

`c/bbu/<Names.isSpilled>.S`: no frame, no call, no store. It tests the kind byte and the opcode
byte of the slot, and reads the byte `m_spills[payload]` for a variable.

The callers are `produce` (the slot `m_target[t]`) and `buildBottomUp` (a target slot). The slot
is a target word, so its id is in `splIds` (`isSpilledA`), and the view holds the byte.
The callers use `g' = g` and the result bit in `al`.
-/

namespace Bbu.Unit

theorem isSpilled_unit [Host] [FunDecls] : UnitThm isSpilledAsm isSpilledA 0 isSpilledQ := by
  sorry

end Bbu.Unit
