import Shuffler.Optimality.BirthPlacement.SourceLazy.WeightBound

namespace Tests.OptimalitySourceLazyCycles

open Shuffler.Optimality.BirthPlacement Shuffler.Permute.Permutation SourceLazy

private def late : Equiv.Perm (Fin 18) :=
  Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ * Equiv.swap ⟨0, by decide⟩ ⟨17, by decide⟩
private def early : Equiv.Perm (Fin 18) :=
  Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ * Equiv.swap ⟨0, by decide⟩ ⟨16, by decide⟩
private def oldPair : Equiv.Perm (Fin 18) := Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩
private def futurePair : Equiv.Perm (Fin 18) := Equiv.swap ⟨16, by decide⟩ ⟨17, by decide⟩
private def initialTop : Equiv.Perm (Fin 18) :=
  Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩ * Equiv.swap ⟨0, by decide⟩ ⟨17, by decide⟩

-- A top at min(old)+16 can close the cycle. One step later forces entry.
example : BirthDeadlines 16 early := by decide
example : Ready 16 3 early ⟨16, by decide⟩ := by decide
example : (forcedCycles 16 3 early).card = 0 := by decide
example : BirthDeadlines 16 late := by decide
example : ¬Ready 16 3 late ⟨17, by decide⟩ := by decide
example : (forcedCycles 16 3 late).card = 1 := by decide
example : interiorEdges 3 late = {⟨1, by decide⟩} := by decide
example : swapBound 16 3 late = 4 := by decide
example : weightScore 3 late = 4 := by decide

example : (forcedCycles 16 3 (eraseTop late ⟨17, by decide⟩)).card =
    (forcedCycles 16 3 late).card :=
  forcedCycles_eraseTop_card late ⟨17, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide)

example : forcedCycles 16 3 (eraseCycle early ⟨16, by decide⟩) = forcedCycles 16 3 early :=
  forcedCycles_eraseCycle early ⟨16, by decide⟩ (by decide) (by decide)

example : arbitrarySwapCount (eraseCycle early ⟨16, by decide⟩) +
    arbitrarySwapCount (early.cycleOf ⟨16, by decide⟩) = arbitrarySwapCount early :=
  eraseCycle_rank early ⟨16, by decide⟩

-- A second future vertex also prevents early closure. Erasing the top
-- of this future-only transposition removes the cycle but preserves q=0.
example : ¬Ready 16 3 futurePair ⟨17, by decide⟩ := by decide
example : eraseTop futurePair ⟨17, by decide⟩ = 1 := by decide
example : (forcedCycles 16 3 (eraseTop futurePair ⟨17, by decide⟩)).card =
    (forcedCycles 16 3 futurePair).card :=
  forcedCycles_eraseTop_card futurePair ⟨17, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- A late cycle that contains the original source top is not forced.
example : ¬Ready 16 3 initialTop ⟨17, by decide⟩ := by decide
example : (forcedCycles 16 3 initialTop).card = 0 := by decide
example : (forcedCycles 16 3 (eraseTop initialTop ⟨17, by decide⟩)).card =
    (forcedCycles 16 3 initialTop).card :=
  forcedCycles_eraseTop_card initialTop ⟨17, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- No-growth cycles away from the source top pay the existing star cost.
example : (forcedCycles 16 3 oldPair).card = 1 := by decide
example : swapBound 16 3 oldPair = 3 := by decide
example : forcedCycles 16 3 oldPair = cyclesAwayFromTop oldPair ⟨2, by decide⟩ :=
  forcedCycles_at_source oldPair (by decide) (by decide) (by decide)

example : (forcedCycles 16 0 late).card = 0 := by decide
example : (forcedCycles 16 1 late).card = 0 := by decide
example : (forcedCycles 0 0 (1 : Equiv.Perm (Fin 0))).card = 0 := by decide
example : swapBound 16 18 (1 : Equiv.Perm (Fin 18)) = 0 := by decide
example : weightScore 0 late = late.support.card := by decide
example : weightScore 1 late = late.support.card := by decide

example : swapBound 16 3 late ≤ weightScore 3 late :=
  swapBound_le_weightScore late (by decide)
example : (forcedCycles 16 3 oldPair).card ≤ (interiorEdges 3 oldPair).card :=
  forcedCycles_card_le_interiorEdges oldPair (by decide)

#print axioms forcedCycles_eraseTop_card
#print axioms forcedCycles_eraseCycle
#print axioms eraseCycle_rank
#print axioms forcedCycles_at_source
#print axioms forcedCycles_card_le_interiorEdges
#print axioms swapBound_le_weightScore

end Tests.OptimalitySourceLazyCycles
