import Shuffler.Resolve.Defs

namespace Shuffler.Planner

variable {source target : Stack}

-- A value can be generated, loaded from a spill, or read from an undropped source slot.
-- This does not require the source slot to be within DUP reach.
def State.Available (state : State source target) (value : Value) : Prop :=
  value.can_be_freely_generated ∨ state.spills.is_spilled value ∨
    ∃ i : Fin source.length, state.dropped[i] = 0 ∧ source[i] = value

-- Every required target value is available.
def State.TargetAvailable (state : State source target) : Prop :=
  ∀ value ∈ target, ¬ value.is_junk → state.Available value

-- Every source slot with a destination in the mapping has its dropped flag set to zero.
def State.RetainedUndropped (state : State source target)
    (mapping : Mapping source.length target.length) : Prop :=
  ∀ i, (mapping.destinationOf i).isSome → state.dropped[i] = 0

-- Count dropped source positions. Every nonzero flag denotes a drop.
def State.droppedCount (state : State source target) : ℕ :=
  (Finset.univ.filter (fun i : Fin source.length => state.dropped[i] ≠ 0)).card

end Shuffler.Planner
