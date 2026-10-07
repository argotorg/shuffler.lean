import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

namespace Shuffler.Optimality.BirthPlacement.Reservations

def Covers (reach start cut : Nat) : Prop := start ≤ cut ∧ cut < start + reach

instance (reach start cut : Nat) : Decidable (Covers reach start cut) := by
  unfold Covers
  infer_instance

def load (reach : Nat) (selected : Finset Nat) (cut : Nat) : Nat :=
  (selected.filter fun start => Covers reach start cut).card

def Feasible (reach : Nat) (capacity : Nat → Nat) (selected : Finset Nat) : Prop :=
  ∀ cut, load reach selected cut ≤ capacity cut

def Available (reach : Nat) (capacity : Nat → Nat) (start : Nat) : Prop :=
  ∀ cut ∈ Finset.Ico start (start + reach), 0 < capacity cut

instance (reach : Nat) (capacity : Nat → Nat) (start : Nat) :
    Decidable (Available reach capacity start) := by
  unfold Available
  infer_instance

def reserve (reach : Nat) (capacity : Nat → Nat) (start cut : Nat) : Nat :=
  capacity cut - if Covers reach start cut then 1 else 0

-- Candidates are processed in increasing order. Each accepted interval has
-- the same length, so an earlier accepted interval ends no later.
def select (reach : Nat) (capacity : Nat → Nat) : List Nat → Finset Nat
  | [] => ∅
  | start :: rest =>
      if Available reach capacity start then
        insert start (select reach (reserve reach capacity start) rest)
      else select reach capacity rest

end Shuffler.Optimality.BirthPlacement.Reservations
