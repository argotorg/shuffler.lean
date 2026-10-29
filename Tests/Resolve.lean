import Shuffler.Resolve.Defs

namespace ResolveTests

private def source : Stack :=
  [.Var ⟨1⟩, .Var ⟨2⟩, .Var ⟨3⟩, .Var ⟨0⟩, .Var ⟨0⟩]

private def target : Stack :=
  [.Var ⟨0⟩, .Var ⟨2⟩, .Var ⟨3⟩, .Var ⟨0⟩, .Var ⟨1⟩]

private def mapping : Mapping source.length target.length :=
  (Equiv.swap (0 : Fin 5) (4 : Fin 5)).toPEquiv

private def run (excess : ℕ) (spillingAllowed : Bool) (spills : SpillSet := ∅)
    (blockedOffset : ℕ := 0) : Except ShuffleErr (Bool × SpillSet × List ℕ) :=
  let init : Shuffler.Planner.State source target :=
    { spills, spillingAllowed, dropped := Vector.replicate source.length 0 }
  (Shuffler.Planner.resolve init mapping ⟨blockedOffset, excess⟩ mapping).map
    (fun (success, state) => (success, state.spills, state.dropped.toList.map Fin.val))

-- No drops are needed when excess is zero.
example : run 0 false = .ok (true, ∅, [0, 0, 0, 0, 0]) := by
  native_decide

-- Equal classes prefer the copy bound for the higher target offset.
example : run 1 false = .ok (true, ∅, [0, 0, 0, 1, 0]) := by
  native_decide

-- After dropping one copy, the last copy cannot be dropped without spilling.
example : run 2 false = .ok (false, ∅, [0, 0, 0, 1, 0]) := by
  native_decide

-- Reclassify after the first drop and spill the highest remaining target.
example : run 2 true = .ok (true, {⟨3⟩}, [0, 0, 1, 1, 0]) := by
  native_decide

-- Both copies can be dropped when their value was already spilled.
example : run 2 false {⟨0⟩} = .ok (true, {⟨0⟩}, [0, 0, 0, 1, 1]) := by
  native_decide

-- An empty candidate range cannot provide a drop.
example : run 1 false (blockedOffset := 4) = .ok (false, ∅, [0, 0, 0, 0, 0]) := by
  native_decide

end ResolveTests
