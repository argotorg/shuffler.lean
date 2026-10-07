import Shuffler.Optimality.BirthPlacement.Schedule
import Shuffler.Placement.Build

namespace Shuffler.Optimality.BirthPlacement

inductive BirthMethod where
  | direct
  | dup
  deriving DecidableEq

def birthWord (target : Stack) (assignment : Equiv.Perm (Fin target.length)) : Stack :=
  List.ofFn fun index => target[assignment index]

def prefixValues (target : Stack) (permutation : Equiv.Perm (Fin target.length))
    (height : Nat) : Stack := (birthWord target permutation).take height

def BirthAvailable (spills : SpillSet) (target births : Stack) (height : Nat)
    (value : Value) : BirthMethod → Prop
  | .direct => Shuffler.Placement.Free spills value
  | .dup => (target.take (height - 16)).count value < (births.take height).count value

instance (spills : SpillSet) (target births : Stack) (height : Nat)
    (value : Value) (method : BirthMethod) :
    Decidable (BirthAvailable spills target births height value method) := by
  cases method <;> unfold BirthAvailable <;> infer_instance

-- A plan specifies values and instruction kinds before stack construction.
-- Its conditions use only this data and target prefix counts.
structure Plan (spills : SpillSet) (target : Stack) where
  assignment : Equiv.Perm (Fin target.length)
  method : Fin target.length → BirthMethod
  deadlines : BirthDeadlines 16 assignment
  available : ∀ index : Fin target.length,
    BirthAvailable spills target (birthWord target assignment) index.val
      target[assignment index] (method index)

end Shuffler.Optimality.BirthPlacement
