import Skel.Gen.Derive.Blocks
import Lift.Level3.L1

/-! The derived blocks of the 8 pilot functions of `Lift.Level3.Code.code` (benchmark level 3; task N11). -/

namespace Skel.Gen.Derived

#derive_blocks pilot Lift.Level3.L1.step Lift.Level3.Code.code ["solidity_shuffler_workspaceAlignment",
  ".Lshuffler.SpillSet.add", ".Lshuffler.Emission.shallowestCopyPosition", ".Lshuffler.Emission.pop",
  ".Lshuffler.Planner.isRetained", ".Lshuffler.MappingBuilder.map", ".Lshuffler.MappingBuilder.closestCopy",
  ".Lshuffler.MappingBuilder.mapInPlace"]

end Skel.Gen.Derived
