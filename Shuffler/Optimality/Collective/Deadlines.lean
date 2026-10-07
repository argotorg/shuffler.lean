import Shuffler.Optimality.Collective.Inventory
import Batteries.Data.List.Count

namespace Shuffler.Optimality.Collective

-- The first source.count value occurrences use old copies. Each later
-- occurrence needs a new copy, so it is a unit birth job.
def newPositions (source target : Stack) : Finset (Fin target.length) :=
  Finset.univ.filter fun index =>
    source.count target[index] ≤ target.countBefore target[index] index.val

def newBefore (source target : Stack) (cut : Nat) : Finset (Fin target.length) :=
  (newPositions source target).filter fun index => index.val < cut

-- Without a retained interval, use the output position's own deadline.
-- A retained interval advances its stop job to its start's deadline.
def deadlineOrigin (selected : Finset (Interval target)) (index : Fin target.length) : Nat :=
  let starts := (selected.filter fun gap => gap.stop = index).image fun gap => gap.start.val
  (insert index.val starts).min' ⟨index.val, Finset.mem_insert_self _ _⟩

def birthDeadline (reach sourceLength : Nat) (selected : Finset (Interval target))
    (index : Fin target.length) : Int :=
  (deadlineOrigin selected index : Int) + reach - sourceLength + 1

def dueBefore (source target : Stack) (selected : Finset (Interval target))
    (cut : Nat) : Finset (Fin target.length) :=
  (newPositions source target).filter fun index => deadlineOrigin selected index < cut

end Shuffler.Optimality.Collective
