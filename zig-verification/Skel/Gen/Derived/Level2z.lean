import Skel.Gen.Derive.Blocks
import Lift.Level2z.L1

/-! The derived blocks of the 17 functions of `Lift.Level2z.Code.code` (benchmark level 2 in Zig, task L2Z-0): the block
source of `generate` for level2z. -/

namespace Skel.Gen.Derived

#derive_blocks level2z Lift.Level2z.L1.step Lift.Level2z.Code.code ["l2zFlags", "l2zBits", "l2zArith", "l2zNarrow",
  "l2zField", "l2zPtrStore", "l2zIdxPush", "l2zIdxPop", "l2zTwoLoops", "l2zNest", "l2zExit3", "l2zFrame", "l2zArgs8",
  "l2zStackCaller", "l2zWrap", "l2zCallLoop", "l2zAlias"]

end Skel.Gen.Derived
