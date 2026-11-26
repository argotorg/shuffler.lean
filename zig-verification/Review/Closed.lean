-- Closed final contracts from the paused campaign.
import LeanTools.Axioms
import Lift.Shuffler.Proved.emissionDup
import Lift.Shuffler.Proved.emissionIsAvailable
import Lift.Shuffler.Proved.emissionIsSpilled
import Lift.Shuffler.Proved.emissionPop
import Lift.Shuffler.Proved.emissionPush
import Lift.Shuffler.Proved.emissionShallowestCopyPosition
import Lift.Shuffler.Proved.emissionSwapWith
import Lift.Shuffler.Proved.mappingBuilderAbsorbSurplus
import Lift.Shuffler.Proved.mappingBuilderClosestCopy
import Lift.Shuffler.Proved.mappingBuilderKeepWildcardSlots
import Lift.Shuffler.Proved.mappingBuilderMap
import Lift.Shuffler.Proved.mappingBuilderMapClosestCopies
import Lift.Shuffler.Proved.mappingBuilderMapInPlace
import Lift.Shuffler.Proved.mappingBuilderMapWildcardSlotCopies
import Lift.Shuffler.Proved.plannerClassify
import Lift.Shuffler.Proved.plannerHasOtherRetainedCopy
import Lift.Shuffler.Proved.plannerIsDemanded
import Lift.Shuffler.Proved.plannerIsRetained
import Lift.Shuffler.Proved.spillSetAdd
import Lift.Shuffler.Proved.workspaceAlignment
import Lift.Shuffler.Proved.workspaceSize

namespace ShufflerZigReview

theorem emissionDup : Lift.Shuffler.Internal.Proposed.DupStatement.DupStatement :=
  Skel.Gen.Level3.Shuffler.emissionDup.skel_semantic.final
#gate_axioms emissionDup

theorem emissionIsAvailable : Lift.Shuffler.Internal.Proposed.IsAvailableStatement.IsAvailableStatement :=
  Skel.Gen.Level3.Shuffler.emissionIsAvailable.skel_semantic.final
#gate_axioms emissionIsAvailable

theorem emissionIsSpilled : Lift.Shuffler.Internal.Proposed.IsSpilledStatement.IsSpilledStatement :=
  Skel.Gen.Level3.Shuffler.emissionIsSpilled.skel_semantic.final
#gate_axioms emissionIsSpilled

theorem emissionPop : Lift.Shuffler.Internal.PopStatement.PopStatement :=
  Skel.Gen.Level3.Shuffler.emissionPop.skel_semantic.final
#gate_axioms emissionPop

theorem emissionPush : Lift.Shuffler.Internal.Proposed.PushStatement.PushStatement :=
  Skel.Gen.Level3.Shuffler.emissionPush.skel_semantic.final
#gate_axioms emissionPush

theorem emissionShallowestCopyPosition : Lift.Shuffler.Internal.ShallowestStatement.ShallowestStatement :=
  Skel.Gen.Level3.Shuffler.emissionShallowestCopyPosition.skel_semantic.final
#gate_axioms emissionShallowestCopyPosition

theorem emissionSwapWith : Lift.Shuffler.Internal.Proposed.SwapWithStatement.SwapWithStatement :=
  Skel.Gen.Level3.Shuffler.emissionSwapWith.skel_semantic.final
#gate_axioms emissionSwapWith

theorem mappingBuilderAbsorbSurplus : Lift.Shuffler.Internal.Proposed.AbsorbSurplusStatement.AbsorbSurplusStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderAbsorbSurplus.skel_semantic.final
#gate_axioms mappingBuilderAbsorbSurplus

theorem mappingBuilderClosestCopy : Lift.Shuffler.Internal.ClosestCopyStatement.ClosestCopyStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderClosestCopy.skel_semantic.final
#gate_axioms mappingBuilderClosestCopy

theorem mappingBuilderKeepWildcardSlots : Lift.Shuffler.Internal.Proposed.KeepWildcardSlotsStatement.KeepWildcardSlotsStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderKeepWildcardSlots.skel_semantic.final
#gate_axioms mappingBuilderKeepWildcardSlots

theorem mappingBuilderMap : Lift.Shuffler.Internal.MapStatement.MapStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderMap.skel_semantic.final
#gate_axioms mappingBuilderMap

theorem mappingBuilderMapClosestCopies : Lift.Shuffler.Internal.Proposed.MapClosestCopiesStatement.MapClosestCopiesStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderMapClosestCopies.skel_semantic.final
#gate_axioms mappingBuilderMapClosestCopies

theorem mappingBuilderMapInPlace : Lift.Shuffler.Internal.MapInPlaceStatement.MapInPlaceStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderMapInPlace.skel_semantic.final
#gate_axioms mappingBuilderMapInPlace

theorem mappingBuilderMapWildcardSlotCopies : Lift.Shuffler.Internal.Proposed.MapWildcardSlotCopiesStatement.MapWildcardSlotCopiesStatement :=
  Skel.Gen.Level3.Shuffler.mappingBuilderMapWildcardSlotCopies.skel_semantic.final
#gate_axioms mappingBuilderMapWildcardSlotCopies

theorem plannerClassify : Lift.Shuffler.Internal.Proposed.ClassifyStatement.ClassifyStatement :=
  Skel.Gen.Level3.Shuffler.plannerClassify.skel_semantic.final
#gate_axioms plannerClassify

theorem plannerHasOtherRetainedCopy : Lift.Shuffler.Internal.Proposed.HasOtherRetainedCopyStatement.HasOtherRetainedCopyStatement :=
  Skel.Gen.Level3.Shuffler.plannerHasOtherRetainedCopy.skel_semantic.final
#gate_axioms plannerHasOtherRetainedCopy

theorem plannerIsDemanded : Lift.Shuffler.Internal.Proposed.IsDemandedStatement.IsDemandedStatement :=
  Skel.Gen.Level3.Shuffler.plannerIsDemanded.skel_semantic.final
#gate_axioms plannerIsDemanded

theorem plannerIsRetained : Lift.Shuffler.Internal.IsRetainedStatement.IsRetainedStatement :=
  Skel.Gen.Level3.Shuffler.plannerIsRetained.skel_semantic.final
#gate_axioms plannerIsRetained

theorem spillSetAdd : Lift.Shuffler.Internal.AddStatement.AddStatement :=
  Skel.Gen.Level3.Shuffler.spillSetAdd.skel_semantic.final
#gate_axioms spillSetAdd

theorem workspaceAlignment : Lift.Shuffler.Internal.AlignmentStatement.AlignmentStatement :=
  Skel.Gen.Level3.Shuffler.workspaceAlignment.skel_semantic.final
#gate_axioms workspaceAlignment

theorem workspaceSize : Lift.Shuffler.Internal.Proposed.WorkspaceSizeStatement.WorkspaceSizeStatement :=
  Skel.Gen.Level3.Shuffler.workspaceSize.skel_semantic.final
#gate_axioms workspaceSize

end ShufflerZigReview
