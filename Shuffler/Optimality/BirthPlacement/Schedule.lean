import Shuffler.Permute.Optimality

namespace Shuffler.Optimality.BirthPlacement

structure TokenRun (size : Nat) where
  permutation : Equiv.Perm (Fin size)
  swaps : List (Fin size × Fin size)

-- Only the current top can move backwards. Each step puts it in its final slot.
-- The token brought to the top can then need the same operation.
def settleTop (permutation : Equiv.Perm (Fin size)) (top : Fin size) : TokenRun size :=
  if _hback : permutation top < top then
    let next := settleTop (permutation * Equiv.swap top (permutation top)) top
    ⟨next.permutation, (top, permutation top) :: next.swaps⟩
  else ⟨permutation, []⟩
termination_by Shuffler.Permute.Permutation.arbitrarySwapCount permutation
decreasing_by
  have hne : permutation top ≠ top := ne_of_lt _hback
  have := Shuffler.Permute.Permutation.arbitrarySwapCount_place_top permutation top hne
  omega

-- Process birth positions from left to right. The swaps for birth j occur
-- before birth j+1. No search over stack states occurs in this construction.
def scheduleFrom (height : Nat) (permutation : Equiv.Perm (Fin size)) : TokenRun size :=
  if hheight : height < size then
    let step := settleTop permutation ⟨height, hheight⟩
    let rest := scheduleFrom (height + 1) step.permutation
    ⟨rest.permutation, step.swaps ++ rest.swaps⟩
  else ⟨permutation, []⟩
termination_by size - height

def schedule (permutation : Equiv.Perm (Fin size)) : TokenRun size :=
  scheduleFrom 0 permutation

def ForwardBefore (permutation : Equiv.Perm (Fin size)) (height : Nat) : Prop :=
  ∀ index : Fin size, index.val < height → index ≤ permutation index

def BirthDeadlines (reach : Nat) (permutation : Equiv.Perm (Fin size)) : Prop :=
  ∀ index : Fin size, index.val ≤ (permutation index).val + reach

instance (reach : Nat) (permutation : Equiv.Perm (Fin size)) :
    Decidable (BirthDeadlines reach permutation) := by unfold BirthDeadlines; infer_instance

end Shuffler.Optimality.BirthPlacement
