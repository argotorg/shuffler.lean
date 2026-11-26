import Skel.Gen.Derive.Blocks
import Lift.Shuffler.L1

/-! Part C of the derived blocks of the full shuffler `Lift.Shuffler.Code.code` (SH-C, N16): 10 functions, one command
each, at the default limits (made by `scratch/n16/mkderived.py`). `Skel/Gen/Derived/Shuffler.lean` joins the three parts. -/

namespace Skel.Gen.Derived

#derive_blocks shuffler_emissionPermuteAtLowestHeight Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.permuteAtLowestHeight"]

#derive_blocks shuffler_emissionRemoveSurplus Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Emission.removeSurplus"]

#derive_blocks shuffler_plannerClassify Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Planner.classify"]

#derive_blocks shuffler_plannerHasOtherRetainedCopy Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.Planner.hasOtherRetainedCopy"]

#derive_blocks shuffler_mappingBuilderAbsorbSurplus Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.absorbSurplus"]

#derive_blocks shuffler_mappingBuilderKeepWildcardSlots Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.keepWildcardSlots"]

#derive_blocks shuffler_mappingBuilderMapWildcardSlotCopies Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.mapWildcardSlotCopies"]

#derive_blocks shuffler_mappingBuilderMapClosestCopies Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.mapClosestCopies"]

#derive_blocks shuffler_mappingBuilderClosestCopy Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.closestCopy"]

#derive_blocks shuffler_mappingBuilderMapInPlace Lift.Shuffler.L1.step Lift.Shuffler.Code.code [".Lshuffler.MappingBuilder.mapInPlace"]

def shufflerC : Derived := shuffler_emissionPermuteAtLowestHeight ++ shuffler_emissionRemoveSurplus ++ shuffler_plannerClassify ++ shuffler_plannerHasOtherRetainedCopy ++ shuffler_mappingBuilderAbsorbSurplus ++ shuffler_mappingBuilderKeepWildcardSlots ++ shuffler_mappingBuilderMapWildcardSlotCopies ++ shuffler_mappingBuilderMapClosestCopies ++ shuffler_mappingBuilderClosestCopy ++ shuffler_mappingBuilderMapInPlace

end Skel.Gen.Derived
