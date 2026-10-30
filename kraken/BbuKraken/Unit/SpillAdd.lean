import BbuKraken.Unit.SpillDefs
import BbuKraken.Unit.IsSpilled

/-!
# `SpillSet::add`

`c/bbu/<Names.spillSetAdd>.S`: no frame, no call. It tests the kind byte and the opcode byte of
the slot (as `isSpilled`), reads the byte `m_spilled[payload]` and, if it is 0, stores 1 to it.
`al` is the `Status`: 0 (`DONE`) or 2 (`ASSERTION_FAILED`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

theorem spillSetAdd_unit [Host] [FunDecls] :
    ∀ p S f n F, Body spillSetAddAsm (AddPre p S f n F) (AddPost p S f n F) := by
  sorry

end Bbu.Unit
