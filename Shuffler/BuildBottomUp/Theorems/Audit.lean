module

import all Shuffler.BuildBottomUp.Theorems.Safety
import all Shuffler.BuildBottomUp.Theorems.Static
import all Shuffler.BuildBottomUp.Theorems.Reachability
import all Shuffler.BuildBottomUp.Theorems.Small
import all Batteries.Tactic.PrintOpaques

import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.Range.Basic
import all Init.Data.List.Sort.Basic

import all Init.Prelude

@[expose] public section

namespace Shuffler.Emission

-- Audit the whole function, including the recursion and the action helpers.
/-- info: 'Shuffler.Emission.buildBottomUp' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques buildBottomUp

/-- info: 'Shuffler.Emission.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

/-- info: 'Shuffler.Emission.buildBottomUp_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_no_assertion

/-- info: 'Shuffler.Emission.loop_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_no_assertion

/-- info: 'Shuffler.Emission.buildBottomUp_correct_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_of_ok

/-- info: 'Shuffler.Emission.buildBottomUp_correct_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_small

/-- info: 'Shuffler.Emission.buildBottomUp_correct_within_dup_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_within_dup_reach

/-- info: 'Shuffler.Emission.buildBottomUp_reachable_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_reachable_of_ok

/-- info: 'Shuffler.Emission.buildBottomUp_succeeds_iff_reachable_of_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_succeeds_iff_reachable_of_processed

/-- info: 'Shuffler.Emission.buildBottomUp_correct_iff_reachable_of_processed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_iff_reachable_of_processed

/-- info: 'Shuffler.Emission.buildBottomUp_succeeds_iff_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_succeeds_iff_static

/-- info: 'Shuffler.Emission.buildBottomUp_correct_iff_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_correct_iff_static

end Shuffler.Emission
