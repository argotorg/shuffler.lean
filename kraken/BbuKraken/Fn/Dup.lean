import BbuKraken.Fn.PushDup

/-!
The body triple of `dup` (`c/bbu/<Names.dup>.S`). `dup` has no frame and no call: it reads
`m_positionOf[d]`, and if it is `-1` it writes the new slot, the operation and the counters.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

open Kit PushDup

-- The asm of `dup` changed with the C++ build (`c/build_bottom_up.cpp`): the struct
-- layout, the `Status` result in `al` and the code. The proof for the C build is in git at 6f580e5.
-- `dup` does the stack operation first, then the assert and the bind (as solc and
-- Model.lean `add`). On
-- `AssertionFailed` the stack has one more slot; `dupR` allows it.
theorem dup_body [Host] [FunDecls] : Body dupAsm dupF dupA dupR := by
  sorry -- wf:todo

end Bbu
