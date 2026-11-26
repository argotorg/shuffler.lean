import Skel.Gen.Derive.Blocks
import Lift.Shuffler.L1

/-! Part A of the derived blocks of the full shuffler `Lift.Shuffler.Code.code` (SH-C, N16): 12 functions, one command
each, at the default limits (made by `scratch/n16/mkderived.py`). `Skel/Gen/Derived/Shuffler.lean` joins the three parts. -/

namespace Skel.Gen.Derived

#derive_blocks shuffler_shuffle Lift.Shuffler.L1.step Lift.Shuffler.Code.code ["solidity_shuffler_shuffle"]

#derive_blocks shuffler_emissionBuildBottomUp Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.buildBottomUp"]

#derive_blocks shuffler_workspaceAlignment Lift.Shuffler.L1.step Lift.Shuffler.Code.code ["solidity_shuffler_workspaceAlignment"]

#derive_blocks shuffler_workspaceSize Lift.Shuffler.L1.step Lift.Shuffler.Code.code ["solidity_shuffler_workspaceSize"]

#derive_blocks shuffler_spillSetAdd Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.SpillSet.add"]

#derive_blocks shuffler_plannerIsRetained Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Planner.isRetained"]

#derive_blocks shuffler_mappingBuilderMap Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.map"]

#derive_blocks shuffler_emissionShallowestCopyPosition Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.shallowestCopyPosition"]

#derive_blocks shuffler_emissionPop Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.pop"]

#derive_blocks shuffler_emissionIsSpilled Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.isSpilled"]

#derive_blocks shuffler_emissionRun Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.run"]

#derive_blocks shuffler_emissionSwapWith Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.swapWith"]

def shufflerA : Derived := shuffler_shuffle ++ shuffler_emissionBuildBottomUp ++ shuffler_workspaceAlignment ++ shuffler_workspaceSize ++ shuffler_spillSetAdd ++ shuffler_plannerIsRetained ++ shuffler_mappingBuilderMap ++ shuffler_emissionShallowestCopyPosition ++ shuffler_emissionPop ++ shuffler_emissionIsSpilled ++ shuffler_emissionRun ++ shuffler_emissionSwapWith

end Skel.Gen.Derived
