import Shuffler.Optimality.BirthPlacement.Reservations

namespace Shuffler.Optimality.BirthPlacement.Hall

def born (positions : Finset Nat) (cut : Nat) : Finset Nat :=
  positions.filter fun position => position ≤ cut

-- Use addition here: truncated subtraction would count output zero too
-- early when cut is less than the reach.
def due (reach : Nat) (positions : Finset Nat) (cut : Nat) : Finset Nat :=
  positions.filter fun position => position + reach ≤ cut

def Condition (reach : Nat) (births outputs : Finset Nat) : Prop :=
  ∀ cut, (due reach outputs cut).card ≤ (born births cut).card

def slack (reach : Nat) (births outputs : Finset Nat) (cut : Nat) : Nat :=
  (born births cut).card - (due reach outputs cut).card

def fixed (reach : Nat) (births outputs : Finset Nat) : Finset Nat :=
  Reservations.select reach (slack reach births outputs) ((births ∩ outputs).sort (· ≤ ·))

def ordered (births outputs : Finset Nat) (hcard : births.card = outputs.card) : births ≃o outputs :=
  (births.orderIsoOfFin rfl).symm.trans (outputs.orderIsoOfFin hcard.symm)

end Shuffler.Optimality.BirthPlacement.Hall
