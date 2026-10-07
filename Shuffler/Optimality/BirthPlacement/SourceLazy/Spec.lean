import Shuffler.Optimality.BirthPlacement.SourcePrefix.Cost

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation

-- A source position must move before any future top in its cycle exists.
-- The initial source top is also outside the cycle.
def Forced (reach height : Nat) (cycle : Equiv.Perm (Fin size)) : Prop :=
  (∀ index ∈ cycle.support, index.val + 1 ≠ height) ∧
    ∃ before ∈ cycle.support, before.val < height ∧
      ∀ next ∈ cycle.support, height ≤ next.val → before.val + reach < next.val

instance (reach height : Nat) (cycle : Equiv.Perm (Fin size)) :
    Decidable (Forced reach height cycle) := by
  unfold Forced
  infer_instance

def forcedCycles (reach height : Nat) (assignment : Equiv.Perm (Fin size)) :
    Finset (Equiv.Perm (Fin size)) :=
  assignment.cycleFactorsFinset.filter (Forced reach height)

-- This is the proposed exact fixed-assignment SWAP count. Its full
-- realization and production-trace lower bound are proof obligations.
def swapBound (reach height : Nat) (assignment : Equiv.Perm (Fin size)) : Nat :=
  arbitrarySwapCount assignment + 2 * (forcedCycles reach height assignment).card

def interiorEdges (height : Nat) (assignment : Equiv.Perm (Fin size)) : Finset (Fin size) :=
  assignment.support.filter fun index =>
    index.val + 1 < height ∧ (assignment index).val + 1 < height

def edgeWeight (height : Nat) (before after : Fin size) : Nat :=
  if before = after then 0
  else if before.val + 1 < height ∧ after.val + 1 < height then 2 else 1

def weightScore (height : Nat) (assignment : Equiv.Perm (Fin size)) : Nat :=
  assignment.support.card + (interiorEdges height assignment).card

-- Reverse one birth: move token top from its current target to the top.
-- After this operation the row top is fixed and can be removed.
def eraseTop (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    Equiv.Perm (Fin size) :=
  Equiv.swap top (assignment top) * assignment

-- The current cycle has no other future vertex, and every old vertex is
-- in the current top's SWAP window. It can be closed before this birth.
def Ready (reach height : Nat) (assignment : Equiv.Perm (Fin size)) (top : Fin size) : Prop :=
  (∀ index ∈ (assignment.cycleOf top).support, height ≤ index.val → index = top) ∧
    ∀ index ∈ (assignment.cycleOf top).support, top.val ≤ index.val + reach

instance (reach height : Nat) (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    Decidable (Ready reach height assignment top) := by
  unfold Ready
  infer_instance

def eraseCycle (assignment : Equiv.Perm (Fin size)) (top : Fin size) :
    Equiv.Perm (Fin size) :=
  (assignment.cycleOf top)⁻¹ * assignment

end Shuffler.Optimality.BirthPlacement.SourceLazy
