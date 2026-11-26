import Lift.Level3.Fast.Code
import Lift.Level3.Fast.Statements.AddStatement
import Lift.Level3.Fast.Statements.AlignmentStatement
import Lift.Level3.Fast.Statements.MapInPlaceStatement
import Lift.P2.Total
import Lift.Pilot.AddSpec
import Lift.Pilot.AddStatement
import Lift.Pilot.AlignmentStatement
import Lift.Pilot.ClosestCopyStatement
import Lift.Pilot.IsRetainedStatement
import Lift.Pilot.MapStatement
import Lift.Pilot.MapInPlaceStatement
import Lift.Pilot.PopStatement
import Lift.Pilot.ShallowestSpec
import Lift.Pilot.ShallowestStatement
import Lift.Pilot.Slot
import Lift.Sem
import Lift.Sem.Bridge
import Lift.Sem.Heap
import Lift.Sem.HeapLemmas
import Lift.Sem.Sim
import Lift.Sem.StackRoom
import Lift.Sem.StackPush
import Lift.Sem.CallArm
import Lift.Sem.SysV
import Lift.Level2z.L1
import Lift.Level2z.Exit3Spec
import Lift.Spike.OuterMem
import Lift.Spike.Sites
import Lift.Spike.Sites.Stack
import Lift.Spike.Sites.Sum
import Lift.Spike.Sum
import Lift.Spike.SumSpec
import Lift.Tactic.Compose
import Lift.Tactic.FrameMem
import Lift.Tactic.FrameMemLemmas
import Lift.Toys.Fast.L1
import Lift.Toys.FillSpec
import Lift.Toys.WalkSpec
import Lift.Trusted.Object
import Skel.Gen.Sites.Level2z
import Skel.Gen.Sites.Pilot
import Skel.Gen.Sites.PilotFast
import Skel.Gen.Sites.Spike
import Skel.Gen.Sites.Toys
import Skel.Gen.Sites.ToysFast
import Skel.Lean.Refute
import Skel.Lean.Sum
import Skel.Gen.Sites.Level2z
import Skel.Test.CallMem.L1
import Lift.Sem.CallMem
import Lift.Sem.CallFrame
import Lift.Pilot.ShallowestSpec
import Skel.Eval.D15Support
import Lift.Shuffler.Zig.Emission
import Lift.Shuffler.Internal.Fns
import Lift.Shuffler.Internal.AddStatement
import Lift.Shuffler.Internal.AlignmentStatement
import Lift.Shuffler.Internal.ClosestCopyStatement
import Lift.Shuffler.Internal.IsRetainedStatement
import Lift.Shuffler.Internal.MapStatement
import Lift.Shuffler.Internal.MapInPlaceStatement
import Lift.Shuffler.Internal.PopStatement
import Lift.Shuffler.Internal.ShallowestStatement
import Lift.Tactic.LoopClose
import Lift.Sem.Final
import Lift.Shuffler.Internal.Proposed.Layout
import Lift.Shuffler.Internal.Proposed.WorkspaceSizeStatement
import Lift.Shuffler.Internal.Proposed.IsSpilledStatement
import Lift.Shuffler.Internal.Proposed.PermuteStatement
import Lift.Shuffler.Internal.Proposed.AbsorbSurplusStatement
import Lift.Shuffler.Internal.Proposed.BuildBottomUpStatement
import Lift.Shuffler.Internal.Proposed.ClassifyStatement
import Lift.Shuffler.Internal.Proposed.DupStatement
import Lift.Shuffler.Internal.Proposed.EmissionRunStatement
import Lift.Shuffler.Internal.Proposed.GenerateStatement
import Lift.Shuffler.Internal.Proposed.HasOtherRetainedCopyStatement
import Lift.Shuffler.Internal.Proposed.IsAvailableStatement
import Lift.Shuffler.Internal.Proposed.IsDemandedStatement
import Lift.Shuffler.Internal.Proposed.KeepWildcardSlotsStatement
import Lift.Shuffler.Internal.Proposed.MapClosestCopiesStatement
import Lift.Shuffler.Internal.Proposed.MapWildcardSlotCopiesStatement
import Lift.Shuffler.Internal.Proposed.PlannerRunStatement
import Lift.Shuffler.Internal.Proposed.ProduceStatement
import Lift.Shuffler.Internal.Proposed.PushStatement
import Lift.Shuffler.Internal.Proposed.RemoveSurplusStatement
import Lift.Shuffler.Internal.Proposed.ResolveStatement
import Lift.Shuffler.Internal.Proposed.SwapWithStatement
import Lift.Shuffler.Zig.Emission
import Lift.Shuffler.Zig.Shuffle
import Skel.Gen.Sites.Shuffler
import Lift.Shuffler.Statement
import Lift.Shuffler.Ext.FlatPlan
import Skel.IntQ.Refute
import Skel.IntQ.RefuteDraw

/-! The modules that the check files of `skel-test` import (`lake env lean` reads their `.olean` files). `lake exe
skel-test` builds the modules that the runner imports, and no others, so a module that only a check file imports stays
unbuilt, or out of date after a change of its source or of its imports (a stale `.olean` that a copy of `.lake` keeps):
the check that imports it then fails, or reads an old file. This library is in `needs` of the executables `skel` and
`skel-test` (`lakefile.toml`), so `lake build skel`, `lake exe skel`, `lake build skel-test` and `lake exe skel-test` build
these modules (RUNG-WIRE: `lake build skel SkelNeeded` did not rebuild `Lift.Tactic.LoopClose`, which only the generated
check files import). The suite `needed`
(`Skel/Test/Needed.lean`) fails when a check file imports a module that is neither here nor imported by `Skel.Test.Main`.
The modules are not imported by the runner, because some of them add parser tokens (`only`, `next`) that break its source. -/
