import Skel.Gen.Derive.Blocks
import Lift.Level3.Fast.L1

/-! The derived blocks of the 8 functions of the ReleaseFast pilot `Lift.Level3.Fast.Code.code` (benchmark level 3, P-FAST). -/

namespace Skel.Gen.Derived

#derive_blocks pilotFast Lift.Level3.Fast.L1.step Lift.Level3.Fast.Code.code ["solidity_shuffler_workspaceAlignment",
  ".Lshuffler.SpillSet.add", ".Lshuffler.Emission.shallowestCopyPosition", ".Lshuffler.Emission.pop",
  ".Lshuffler.Planner.isRetained", ".Lshuffler.MappingBuilder.map", ".Lshuffler.MappingBuilder.closestCopy",
  ".Lshuffler.MappingBuilder.mapInPlace"]

end Skel.Gen.Derived
