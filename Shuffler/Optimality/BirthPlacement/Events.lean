import Shuffler.Optimality.BirthPlacement.Plan
import Shuffler.Optimality.Baseline

namespace Shuffler.Optimality.BirthPlacement

abbrev BirthEvent := BirthMethod × Value

def traceEvents : Trace spills source target → List BirthEvent
  | .Lit _ => []
  | .Swap _ _ _ _ trace => traceEvents trace
  | @Trace.Dup _ _ previous depth _ _ _ trace =>
      traceEvents trace ++ [(.dup, previous[previous.length - depth])]
  | .Pop _ trace => traceEvents trace
  | .Push value _ trace => traceEvents trace ++ [(.direct, value)]
  | .Load id _ trace => traceEvents trace ++ [(.direct, .Var id)]

def Plan.events (plan : Plan spills target) : List BirthEvent :=
  List.ofFn fun index => (plan.method index, target[plan.assignment index])

def eventPrice (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet) : BirthEvent → Nat
  | (.direct, value) => directPrice costs weights spills value
  | (.dup, _) => costs.dup.score weights

def eventScore (costs : PrimitiveCosts) (weights : Weights) (spills : SpillSet)
    (events : List BirthEvent) : Nat := (events.map (eventPrice costs weights spills)).sum

end Shuffler.Optimality.BirthPlacement
