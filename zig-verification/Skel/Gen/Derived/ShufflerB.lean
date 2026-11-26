import Skel.Gen.Derive.Blocks
import Lift.Shuffler.L1

/-! Part B of the derived blocks of the full shuffler `Lift.Shuffler.Code.code` (SH-C, N16): 9 functions, one command
each, at the default limits (made by `scratch/n16/mkderived.py`). `Skel/Gen/Derived/Shuffler.lean` joins the three parts. -/

namespace Skel.Gen.Derived

#derive_blocks shuffler_plannerRun Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Planner.run"]

#derive_blocks shuffler_emissionPermute Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.permute"]

#derive_blocks shuffler_plannerResolve Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Planner.resolve"]

#derive_blocks shuffler_emissionDup Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.dup"]

#derive_blocks shuffler_emissionPush Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.push"]

#derive_blocks shuffler_plannerIsDemanded Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Planner.isDemanded"]

#derive_blocks shuffler_emissionIsAvailable Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.isAvailable"]

#derive_blocks shuffler_emissionGenerate Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.generate"]

#derive_blocks shuffler_emissionProduce Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.produce"]

def shufflerB : Derived := shuffler_plannerRun ++ shuffler_emissionPermute ++ shuffler_plannerResolve ++ shuffler_emissionDup ++ shuffler_emissionPush ++ shuffler_plannerIsDemanded ++ shuffler_emissionIsAvailable ++ shuffler_emissionGenerate ++ shuffler_emissionProduce

end Skel.Gen.Derived
