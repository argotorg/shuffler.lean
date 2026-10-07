import Shuffler.Optimality.BirthPlacement.SourceLazy.Base
import Shuffler.Optimality.BirthPlacement.SourceLazy.Birth

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Placement

variable {spills : SpillSet} {source target : Stack}
  {plan : SourcePlan spills source target}

-- Plan the last birth first. The recursive result supplies its prefix;
-- extend emits that birth and its already-proved local permutation.
def finish (height : Nat) (state : State plan height) : Result plan height state :=
  if he : height = source.length then
    by subst height; exact base state
  else
    match height, state with
    | 0, state => False.elim (he (by have := state.source_le; omega))
    | previous + 1, state =>
      let top : Fin target.length := ⟨previous, by have := state.height_le; omega⟩
      let step := phase top state (by change source.length ≤ previous; have := state.source_le; omega)
      Result.extend top state step (finish previous step.before)
termination_by height

structure Realized (plan : SourcePlan spills source target) where
  built : BuiltTrace spills source target (plan.births : Multiset Value)
  count : built.trace.swapCount = swapBound 16 source.length plan.assignment
  events : traceEvents built.trace = plan.events

def realize (plan : SourcePlan spills source target) : Realized plan := by
  let result := finish target.length (State.initial plan)
  have ht : (State.initial plan).values = target := by simp [State.values, State.initial]
  have hm : (plan.births.take (target.length - source.length) : Multiset Value) = plan.births := by
    simp only [← plan.births_length, List.take_length]
  refine ⟨result.built.cast rfl ht hm, ?_, ?_⟩
  · rw [built_cast_swapCount, result.count]
    rfl
  · rw [built_cast_events, result.events]
    simp only [← plan.events_length, List.take_length]

end Shuffler.Optimality.BirthPlacement.SourceLazy
