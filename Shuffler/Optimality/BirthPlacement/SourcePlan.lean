import Shuffler.Optimality.BirthPlacement.Plan
import Shuffler.Optimality.BirthPlacement.SourcePrefix.Cost
import Shuffler.Optimality.BirthPlacement.SourcePotential

namespace Shuffler.Optimality.BirthPlacement

open Shuffler.Permute.Permutation Shuffler.Placement

def sourceSlot (sourceSize size : Nat) (hle : sourceSize ≤ size)
    (index : Fin (size - sourceSize)) : Fin size :=
  ⟨sourceSize + index.val, by have := index.isLt; omega⟩

-- The source has token identities already. Only the suffix needs birth methods.
structure SourcePlan (spills : SpillSet) (source target : Stack) where
  source_length : source.length ≤ target.length
  assignment : Equiv.Perm (Fin target.length)
  source_values : prefixValues target assignment source.length = source
  deadlines : BirthDeadlines 16 assignment
  source_frozen : ∀ index : Fin target.length,
    index.val + 17 < source.length → assignment index = index
  method : Fin (target.length - source.length) → BirthMethod
  available : ∀ index : Fin (target.length - source.length),
    BirthAvailable spills target (birthWord target assignment) (source.length + index.val)
      target[assignment (sourceSlot source.length target.length source_length index)] (method index)

def SourcePlan.births (plan : SourcePlan spills source target) : Stack :=
  (birthWord target plan.assignment).drop source.length

def SourcePlan.events (plan : SourcePlan spills source target) : List (BirthMethod × Value) :=
  List.ofFn fun index =>
    (plan.method index,
      target[plan.assignment (sourceSlot source.length target.length plan.source_length index)])

def sourceEntryCost (assignment : Equiv.Perm (Fin size)) (height : Nat) (hh : height ≤ size) : Nat :=
  if hz : height = 0 then 0 else
    swapCount (SourcePrefix.permutation assignment height)⁻¹ ⟨height - 1, by omega⟩

structure SourceEntry (plan : SourcePlan spills source target) where
  built : BuiltTrace spills source
    (prefixValues target (SourcePrefix.run plan.assignment source.length).permutation source.length) 0
  count : built.trace.swapCount = sourceEntryCost plan.assignment source.length plan.source_length

end Shuffler.Optimality.BirthPlacement
