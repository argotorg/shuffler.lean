import Shuffler.Optimality.Collective.UnitSchedule

namespace Shuffler.Optimality.Collective

def birthJobs (source target : Stack) : List (Fin target.length) :=
  (List.finRange target.length).filter fun index => index ∈ newPositions source target

def birthOrder (source target : Stack) (selected : Finset (Interval target)) :
    List (Fin target.length) :=
  unitOrder (birthJobs source target) (birthDeadline 16 source.length selected)

end Shuffler.Optimality.Collective
