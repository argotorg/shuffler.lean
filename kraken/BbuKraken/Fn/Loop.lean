import BbuKraken.Fn.Loop.BoundLemmas

/-!
`buildBottomUp` (`c/bbu/<Names.buildBottomUp>.S`) refines `loop` (`Model.loop`) from offset `0`.
The parts of `step` between the cut labels are in `Loop/Defs.lean` and `Loop/Model.lean`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

-- The asm of `buildBottomUp` changed with the C++ build (`c/build_bottom_up.cpp`): the struct
-- layout, the `Status` result in `al` and the code. The proof for the C build is in git at 6f580e5.
-- The bound branch reads `positionOf` two times, asserts `has_value` and `>= targetOffset`,
-- and then asserts `m_stack[pos] == m_stack[sourceForTargetOffset]`. Model.lean `step` and
-- `takeBound` do the same reads and checks in the same order (`bound`, `afterPos`).
-- The calls of `generate` need `0 < pendingGenerations` (`generateA`): it follows from
-- `Inv.len_pending` and `len < n`.
theorem loop_body [Host] [FunDecls]
    (hfin : Spec Names.permute finishF finishA finishR)
    (hspill : Spec Names.isSpilled isSpilledF isSpilledA isSpilledR)
    (hcopy : Spec Names.shallowestCopyPosition shallowestCopyF shallowestCopyA shallowestCopyR)
    (hgen : Spec Names.generate generateF generateA generateR)
    (hswap : Spec Names.swapWith swapWithF swapWithA swapWithR) :
    Body loopAsm loopF loopA loopR := by
  sorry

end Bbu
