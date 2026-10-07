import Shuffler.Optimality.BirthPlacement.Optimize
import Shuffler.Optimality.BirthPlacement.Realize.Theorems
import Shuffler.Optimality.Replay
import Mathlib.GroupTheory.Perm.List

namespace Tests.OptimalityBirthOptimize

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 10
private def b : Value := .Lit 11

-- Equal copies have identities. A supplied plan can move those identities
-- even when every value is already correct. The endpoint optimizer removes
-- all of these moves in this case.
private def equalCopies : Plan ∅ [a, a, a] where
  assignment := List.formPerm [0, 1, 2]
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

#guard equalCopies.assignment.support.card = 3
#guard equalCopies.optimizeEndpoints.assignment.support.card = 0
#guard (realize equalCopies).built.trace.swapCount = 2
#guard flatten (realize equalCopies.optimizeEndpoints).built.trace = [.push a, .push a, .push a]
#guard equalCopies.optimizeEndpoints.events = equalCopies.events

-- Optimizing copy identities keeps the early DUP16 birth before its source
-- leaves DUP reach. The final trace still has the correct output order.
private def boundaryTarget : Stack := [a] ++ List.replicate 16 b ++ [a]
private def boundary : Plan ∅ boundaryTarget where
  assignment := Equiv.swap ⟨16, by decide⟩ ⟨17, by decide⟩
  method := fun index => if index.val = 16 then .dup else .direct
  deadlines := by decide
  available := by decide

#guard birthWord boundaryTarget boundary.optimizeEndpoints.assignment =
  birthWord boundaryTarget boundary.assignment
#guard (flatten (realize boundary.optimizeEndpoints).built.trace).contains (.dup 16)
#guard (replay ∅ [] (flatten (realize boundary.optimizeEndpoints).built.trace)).map (·.target) =
  some boundaryTarget

example (plan : Plan spills target) :
    plan.optimizeEndpoints.assignment.support.card ≤ plan.assignment.support.card :=
  plan.endpointAssignment_support_le plan.assignment (fun _ => rfl) plan.deadlines

end Tests.OptimalityBirthOptimize
