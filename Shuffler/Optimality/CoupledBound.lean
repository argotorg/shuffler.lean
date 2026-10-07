import Shuffler.Optimality.Transport
import Shuffler.Optimality.GapCount.Defs
import Shuffler.Optimality.ForcedIntroduction.CostDefs

namespace Shuffler.Optimality.Capped

structure Choice where
  retain : Nat
  regenerate : Option (Nat × Nat)
  deriving DecidableEq, Repr

-- Every row has K+1 entries. The index is the remaining prepaid SWAP count.
def extend (swapPrice : Nat) (choice : Choice) (previous : Vector Nat (K + 1)) :
    Vector Nat (K + 1) :=
  Vector.ofFn fun cap =>
    let retain := swapPrice * (choice.retain - cap.val) +
      previous[cap.val - choice.retain]'(by omega)
    match choice.regenerate with
    | none => retain
    | some (premium, required) => min retain
        (premium + swapPrice * (required - cap.val) +
          previous[cap.val - required]'(by omega))

def table (swapPrice K : Nat) (choices : List Choice) : Vector Nat (K + 1) :=
  choices.foldr (extend swapPrice) (Vector.replicate (K + 1) 0)

def bound (swapPrice K : Nat) (choices : List Choice) : Nat :=
  swapPrice * K + (table swapPrice K choices)[K]

end Shuffler.Optimality.Capped

namespace Shuffler.Optimality

def coupledValueChoice (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) (value : Value) : Capped.Choice :=
  let transported := Transport.requiredSwaps value source target
  if ForcedIntroduction.Required value source target missing then
    { retain := transported, regenerate := none }
  else
    { retain := max transported (max (Lineage.requiredSwaps value source target missing)
        (GapCount.requiredSwaps value source target))
      regenerate := if Shuffler.Placement.Free spills value ∧ 0 < missing.count value then
        some (directPrice costs weights spills value - unitPrice costs weights spills value, transported)
        else none }

def coupledBound (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack) (missing : Multiset Value) (swapFloor : Nat) : Nat :=
  ForcedIntroduction.bound costs weights spills source target missing +
    Capped.bound (costs.swap.score weights) (min 17 swapFloor)
    (source.dedup.map (coupledValueChoice costs weights spills source target missing))

end Shuffler.Optimality
