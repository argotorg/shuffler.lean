import Skel.Gen.Derive.Blocks
import Lift.Spike.L1

/-! The derived blocks of the functions of `Lift.Spike.Code.code` (task N11): the block source of `generate` for
`toySum` and `toyJob`. -/

namespace Skel.Gen.Derived

#derive_blocks spike Lift.Spike.L1.step Lift.Spike.Code.code ["toyJob", "toySum", "toyTwo", "toyHalf", "toyMark",
  "toyInc"]

end Skel.Gen.Derived
