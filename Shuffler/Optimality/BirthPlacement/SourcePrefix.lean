import Shuffler.Optimality.BirthPlacement.Schedule

namespace Shuffler.Optimality.BirthPlacement.SourcePrefix

-- This is a prefix of the existing virtual birth schedule. It does not emit
-- a trace from a nonempty source or choose a new source scheduling policy.
def run (assignment : Equiv.Perm (Fin size)) : Nat → TokenRun size
  | 0 => ⟨assignment, []⟩
  | height + 1 =>
      let previous := run assignment height
      if h : height < size then
        let next := settleTop previous.permutation ⟨height, h⟩
        ⟨next.permutation, previous.swaps ++ next.swaps⟩
      else previous

def permutation (assignment : Equiv.Perm (Fin size)) (height : Nat) : Equiv.Perm (Fin size) :=
  ((run assignment height).swaps.map fun pair => Equiv.swap pair.1 pair.2).prod

def WithinCycles (assignment state : Equiv.Perm (Fin size)) : Prop :=
  ∀ index, assignment.SameCycle index (state index)

def cyclesIn (state component : Equiv.Perm (Fin size)) (top : Fin size) :
    Finset (Equiv.Perm (Fin size)) :=
  (Shuffler.Permute.Permutation.cyclesAwayFromTop state top).filter
    (fun cycle => cycle.support ⊆ component.support)

def closedPairs (assignment : Equiv.Perm (Fin size)) (height : Nat) (top : Fin size) :
    Finset (Equiv.Perm (Fin size)) :=
  assignment.cycleFactorsFinset.filter (fun cycle =>
    cycle.support.card = 2 ∧ (∀ index ∈ cycle.support, index.val < height) ∧ cycle top = top)

end Shuffler.Optimality.BirthPlacement.SourcePrefix
