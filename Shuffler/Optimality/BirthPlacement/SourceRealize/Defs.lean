import Shuffler.Optimality.BirthPlacement.SourcePlan.Theorems

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation Shuffler.Placement

structure SourceBuildState (plan : SourcePlan spills source target) (height : Nat) where
  source_le : source.length ≤ height
  height_le : height ≤ target.length
  permutation : Equiv.Perm (Fin target.length)
  built : BuiltTrace spills source (prefixValues target permutation height)
    (plan.births.take (height - source.length) : Multiset Value)
  forward : ForwardBefore permutation height
  deadlines : BirthDeadlines 16 permutation
  unborn : ∀ index : Fin target.length, height ≤ index.val → permutation index = plan.assignment index
  count : built.trace.swapCount + arbitrarySwapCount permutation =
    sourcePotential plan.assignment source.length plan.source_length
  events : traceEvents built.trace = plan.events.take (height - source.length)

structure RealizedSourcePlan (plan : SourcePlan spills source target) where
  built : BuiltTrace spills source target (plan.births : Multiset Value)
  count : built.trace.swapCount = sourcePotential plan.assignment source.length plan.source_length
  events : traceEvents built.trace = plan.events

variable {spills : SpillSet} {source target : Stack} {plan : SourcePlan spills source target}
  {height : Nat}

abbrev SourceBuildState.top (_state : SourceBuildState plan height) (hh : height < target.length) :
    Fin target.length := ⟨height, hh⟩

abbrev SourceBuildState.eventIndex (state : SourceBuildState plan height) (hh : height < target.length) :
    Fin (target.length - source.length) := ⟨height - source.length, by have := state.source_le; omega⟩

abbrev SourceBuildState.current (state : SourceBuildState plan height) : Stack :=
  prefixValues target state.permutation height

abbrev SourceBuildState.value (state : SourceBuildState plan height) (hh : height < target.length) : Value :=
  target[plan.assignment (state.top hh)]

abbrev SourceBuildState.method (state : SourceBuildState plan height) (hh : height < target.length) : BirthMethod :=
  plan.method (state.eventIndex hh)

structure SourceBirth (state : SourceBuildState plan height) (hh : height < target.length) where
  built : BuiltTrace spills state.current (prefixValues target state.permutation (height + 1))
    {state.value hh}
  count : built.trace.swapCount = 0
  events : traceEvents built.trace = [(state.method hh, state.value hh)]

end Shuffler.Optimality.BirthPlacement
