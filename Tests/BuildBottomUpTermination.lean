import Shuffler
import Batteries.Tactic.PrintOpaques

open Shuffler.BuildBottomUp

namespace BuildBottomUpTerminationTests

-- Audit the whole function, including the recursion and the action helpers.
/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

-- A body containing another while loop must not pass that dependency check.
def bodyWithNestedLoop (_ : Unit) (control : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) := do
  while true do pure ()
  return .done control

/--
info: 'BuildBottomUpTerminationTests.bodyWithNestedLoop' depends on opaque or partial definitions: [Classical.choice,
 _private.Init.While.0.repeatM.impl]
-/
#guard_msgs in
#print opaques bodyWithNestedLoop

-- Partial code in a helper must also be detected. These functions are never evaluated.
partial def partialHelper (n : ℕ) : ℕ := partialHelper (n + 1)

def bodyWithPartialHelper (_ : Unit) (control : ℕ) : StateT ℕ (Except Error) (ForInStep ℕ) :=
  fun state => .ok (.done (partialHelper control), state)

/-- info: 'BuildBottomUpTerminationTests.bodyWithPartialHelper' depends on opaque or partial definitions: [BuildBottomUpTerminationTests.partialHelper] -/
#guard_msgs in
#print opaques bodyWithPartialHelper

end BuildBottomUpTerminationTests
