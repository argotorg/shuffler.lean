import Shuffler.Optimality.BirthPlacement.Cheapest
import Shuffler.Optimality.BirthPlacement.Events.Theorems
import Mathlib.Algebra.BigOperators.Fin

namespace Shuffler.Optimality.BirthPlacement

theorem cheapestMethod_available (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target births : Stack) (height : Nat) (value : Value) (method : BirthMethod)
    (havailable : BirthAvailable spills target births height value method) :
    BirthAvailable spills target births height value
      (cheapestMethod costs weights spills target births height value) := by
  unfold cheapestMethod
  split_ifs with hdup hcheap
  · exact hcheap.1
  · exact hdup
  · cases method with
    | direct => exact havailable
    | dup => exact False.elim (hdup havailable)

theorem cheapestMethod_price_le (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (target births : Stack) (height : Nat) (value : Value) (method : BirthMethod)
    (havailable : BirthAvailable spills target births height value method) :
    eventPrice costs weights spills
      (cheapestMethod costs weights spills target births height value, value) ≤
        eventPrice costs weights spills (method, value) := by
  unfold cheapestMethod
  split_ifs with hdup hcheap
  · cases method with
    | direct => exact le_rfl
    | dup => exact hcheap.2
  · cases method with
    | direct =>
      have hn : ¬directPrice costs weights spills value ≤ costs.dup.score weights :=
        fun hp => hcheap ⟨havailable, hp⟩
      exact (Nat.lt_of_not_ge hn).le
    | dup => exact le_rfl
  · cases method with
    | direct => exact le_rfl
    | dup => exact False.elim (hdup havailable)

def Plan.cheapest (plan : Plan spills target) (costs : PrimitiveCosts) (weights : Weights) :
    Plan spills target where
  assignment := plan.assignment
  method := fun index => cheapestMethod costs weights spills target
    (birthWord target plan.assignment) index.val target[plan.assignment index]
  deadlines := plan.deadlines
  available := fun index => cheapestMethod_available costs weights spills target
    (birthWord target plan.assignment) index.val target[plan.assignment index]
      (plan.method index) (plan.available index)

theorem Plan.cheapest_eventScore_le (plan : Plan spills target)
    (costs : PrimitiveCosts) (weights : Weights) :
    eventScore costs weights spills (plan.cheapest costs weights).events ≤
      eventScore costs weights spills plan.events := by
  simp only [eventScore, Plan.events, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro index _
  exact cheapestMethod_price_le costs weights spills target (birthWord target plan.assignment)
    index.val target[plan.assignment index] (plan.method index) (plan.available index)

end Shuffler.Optimality.BirthPlacement
