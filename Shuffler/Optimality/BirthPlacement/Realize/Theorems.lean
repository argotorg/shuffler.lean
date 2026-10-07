import Shuffler.Optimality.BirthPlacement.Realize.State
import Shuffler.Optimality.SwapRuns
import Shuffler.Optimality.BirthPlacement.Cheapest.Theorems

namespace Shuffler.Optimality.BirthPlacement

theorem traceEvents_values (trace : Trace spills source target) :
    (traceEvents trace).map Prod.snd = SwapRuns.births trace := by
  induction trace <;> simp_all [traceEvents, SwapRuns.births]

theorem Plan.events_values (plan : Plan spills target) :
    plan.events.map Prod.snd = birthWord target plan.assignment := by
  simp [Plan.events, birthWord, List.map_ofFn, Function.comp_def]

theorem realize_births (plan : Plan spills target) :
    SwapRuns.births (realize plan).built.trace = birthWord target plan.assignment := by
  rw [← traceEvents_values, (realize plan).events, plan.events_values]

theorem realize_score (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target) :
    (traceCost costs (realize plan).built.trace).score weights =
      eventScore costs weights spills plan.events +
        costs.swap.score weights * Shuffler.Permute.Permutation.arbitrarySwapCount plan.assignment := by
  rw [noPop_score costs weights _ (realize plan).built.noPop,
    (realize plan).events, (realize plan).count]

theorem realize_score_le (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target) :
    (traceCost costs (realize plan).built.trace).score weights ≤
      eventScore costs weights spills plan.events + costs.swap.score weights * plan.assignment.support.card := by
  rw [noPop_score costs weights _ (realize plan).built.noPop, (realize plan).events]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (realize_swapCount_le_moved plan)) _

theorem realize_cheapest_score_le (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) :
    (traceCost costs (realize (plan.cheapest costs weights)).built.trace).score weights ≤
      (traceCost costs (realize plan).built.trace).score weights := by
  rw [realize_score, realize_score]
  exact Nat.add_le_add_right (plan.cheapest_eventScore_le costs weights) _

-- The caller supplies the movement and introduction comparisons. This theorem
-- does not assert that a planner finds the required assignment.
theorem realize_score_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (other : Trace spills [] target) (hpop : other.noPop)
    (hintroduction : eventScore costs weights spills plan.events ≤
      eventScore costs weights spills (traceEvents other))
    (hmovement : plan.assignment.support.card ≤ 2 * other.swapCount) :
    (traceCost costs (realize plan).built.trace).score weights ≤
      2 * (traceCost costs other).score weights := by
  apply (realize_score_le costs weights plan).trans
  rw [noPop_score costs weights other hpop]
  have hi := Nat.add_le_add_right hintroduction
    (costs.swap.score weights * plan.assignment.support.card)
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) hmovement
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  omega

theorem realize_surplus_le_twice (costs : PrimitiveCosts) (weights : Weights)
    (plan : Plan spills target) (other : Trace spills [] target) (hpop : other.noPop)
    (base : Nat)
    (hbase : base ≤ eventScore costs weights spills (traceEvents other))
    (hintroduction : eventScore costs weights spills plan.events ≤
      eventScore costs weights spills (traceEvents other))
    (hmovement : plan.assignment.support.card ≤ 2 * other.swapCount) :
    (traceCost costs (realize plan).built.trace).score weights - base ≤
      2 * ((traceCost costs other).score weights - base) := by
  have hscore := realize_score_le costs weights plan
  have hm := Nat.mul_le_mul_left (costs.swap.score weights) hmovement
  rw [Nat.mul_left_comm (costs.swap.score weights) 2] at hm
  rw [noPop_score costs weights other hpop]
  have hbound : (traceCost costs (realize plan).built.trace).score weights ≤
      eventScore costs weights spills (traceEvents other) +
        2 * (costs.swap.score weights * other.swapCount) := by omega
  omega

end Shuffler.Optimality.BirthPlacement
