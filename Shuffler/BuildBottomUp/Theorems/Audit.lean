import Shuffler.BuildBottomUp.Theorems.Safety
import Shuffler.BuildBottomUp.Theorems.Static
import Shuffler.BuildBottomUp.Theorems.Reachability
import Shuffler.BuildBottomUp.Theorems.Small
import Batteries.Tactic.PrintOpaques

namespace Shuffler.BuildBottomUp

-- Audit the whole function, including the recursion and the action helpers.
/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_no_assertion

/-- info: 'Shuffler.BuildBottomUp.loop_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_no_assertion

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_of_ok

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_small

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_within_dup_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_within_dup_reach

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_reachable_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_reachable_of_ok

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_succeeds_iff_reachable_of_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_succeeds_iff_reachable_of_processed

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_iff_reachable_of_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_iff_reachable_of_processed

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_succeeds_iff_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_succeeds_iff_static

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_correct_iff_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_iff_static

end Shuffler.BuildBottomUp
