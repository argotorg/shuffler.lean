import Shuffler.Optimality.Collective.Inventory

namespace Shuffler.Optimality.Collective

def paidIntervals (source target : Stack) : Finset (Interval target) :=
  Finset.univ.filter (Interval.Paid source)

-- The sum condition keeps the height-seventeen obstruction. Subtracting
-- mandatory inventory from sixteen would lose that obstruction in Nat.
def FeasiblePaidIntervals (source target : Stack) (selected : Finset (Interval target)) : Prop :=
  selected ⊆ paidIntervals source target ∧
    ∀ cut : Fin (target.length + 1), 0 < cut.val →
      (mandatory source target cut.val).card +
        (selected.filter fun gap => gap.Crosses cut.val).card ≤ 16

instance (source target : Stack) (selected : Finset (Interval target)) :
    Decidable (FeasiblePaidIntervals source target selected) := by
  unfold FeasiblePaidIntervals
  infer_instance

def UpperInventoryWeight (source target : Stack) (premium : Value → Nat) (bound : Nat) : Prop :=
  ∀ selected : Finset (Interval target), FeasiblePaidIntervals source target selected →
    intervalWeight premium selected ≤ bound

-- Finite specification only. No production planner evaluates this maximum.
def inventoryMaximum (source target : Stack) (premium : Value → Nat) : Nat :=
  ((paidIntervals source target).powerset.filter (FeasiblePaidIntervals source target)).sup
    (intervalWeight premium)

def inventoryFloor (source target : Stack) (premium : Value → Nat) : Nat :=
  intervalWeight premium (paidIntervals source target) - inventoryMaximum source target premium

end Shuffler.Optimality.Collective
