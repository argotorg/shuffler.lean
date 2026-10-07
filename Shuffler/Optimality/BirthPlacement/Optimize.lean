import Shuffler.Optimality.BirthPlacement.Word.Theorems
import Shuffler.Optimality.BirthPlacement.Events

namespace Shuffler.Optimality.BirthPlacement

def Plan.endpointAssignment (plan : Plan spills target) : Equiv.Perm (Fin target.length) :=
  Word.optimal 16 (fun index => target[plan.assignment index]) (fun index => target[index])
    (Word.balanced_of_matching plan.assignment (fun _ => rfl))

theorem Plan.endpointAssignment_value (plan : Plan spills target) (index : Fin target.length) :
    target[plan.endpointAssignment index] = target[plan.assignment index] :=
  (Word.optimal_compatible (Word.balanced_of_matching plan.assignment (fun _ => rfl)) index).symm

theorem Plan.endpointAssignment_birthWord (plan : Plan spills target) :
    birthWord target plan.endpointAssignment = birthWord target plan.assignment := by
  unfold birthWord
  congr 1
  funext index
  exact plan.endpointAssignment_value index

theorem Plan.endpointAssignment_deadlines (plan : Plan spills target) :
    BirthDeadlines 16 plan.endpointAssignment :=
  Word.optimal_deadline (Word.balanced_of_matching plan.assignment (fun _ => rfl))
    (Word.feasible_of_matching plan.assignment (fun _ => rfl) plan.deadlines)

def Plan.optimizeEndpoints (plan : Plan spills target) : Plan spills target where
  assignment := plan.endpointAssignment
  method := plan.method
  deadlines := plan.endpointAssignment_deadlines
  available index := by
    rw [plan.endpointAssignment_birthWord, plan.endpointAssignment_value]
    exact plan.available index

theorem Plan.optimizeEndpoints_events (plan : Plan spills target) :
    plan.optimizeEndpoints.events = plan.events := by
  unfold Plan.events
  congr 1
  funext index
  exact congrArg (plan.method index, ·) (plan.endpointAssignment_value index)

theorem Plan.endpointAssignment_support_le (plan : Plan spills target)
    (other : Equiv.Perm (Fin target.length))
    (hvalues : ∀ index, target[plan.assignment index] = target[other index])
    (hdeadline : BirthDeadlines 16 other) :
    plan.endpointAssignment.support.card ≤ other.support.card :=
  Word.support_card_le (Word.balanced_of_matching plan.assignment (fun _ => rfl))
    other hvalues hdeadline

end Shuffler.Optimality.BirthPlacement
