import Skel.Gen.Derive.Blocks
import Lift.Toys.L1

/-! The derived blocks of the toy functions of `Lift.Toys.Code.code` (task N11): the block source of `generate` for the
toys. -/

namespace Skel.Gen.Derived

#derive_blocks toys Lift.Toys.L1.step Lift.Toys.Code.code ["toyCount", "toyTail", "toyFind", "toyClamp", "toyOuter",
  "toyTwo", "toyHalf", "toyFill", "toyAt", "toyWalk", "toyJob", "toySum", "toyMark", "toyInc"]

end Skel.Gen.Derived
