import Shuffler.Optimality.FrozenPrefix.Theorems
import Shuffler.Optimality.Baseline

namespace Shuffler.Optimality.FrozenPrefix

-- Fewer initial source kinds can only add first-introduction surcharges.
-- This uses natural-number costs, with no EVM-specific price assumption.
theorem baseline_le_of_subset (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source reduced : Stack) (missing : Multiset Value)
    (hsubset : ∀ value ∈ reduced, value ∈ source) :
    baseline costs weights spills source missing ≤ baseline costs weights spills reduced missing := by
  unfold baseline
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro value _
  by_cases hr : value ∈ reduced
  · simp only [hr, hsubset value hr, ↓reduceIte, Nat.le_refl]
  · simp only [hr, ↓reduceIte]
    split <;> omega

theorem baseline_le_drop (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (count : Nat) :
    baseline costs weights spills source missing ≤
      baseline costs weights spills (source.drop count) missing := by
  apply baseline_le_of_subset
  intro value hv
  exact List.mem_of_mem_drop hv

end Shuffler.Optimality.FrozenPrefix
