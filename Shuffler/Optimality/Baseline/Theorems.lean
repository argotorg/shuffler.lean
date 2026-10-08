import Shuffler.Optimality.Baseline
import Shuffler.BuildBottomUp.Lemmas.Placement.TraceInvariants

namespace Shuffler.Optimality

theorem unitPrice_le_dup (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) :
    unitPrice costs weights spills value ≤ costs.dup.score weights :=
  Nat.min_le_left _ _

theorem unitPrice_le_direct (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) :
    unitPrice costs weights spills value ≤ directPrice costs weights spills value :=
  Nat.min_le_right _ _

@[simp] theorem baseline_zero (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) : baseline costs weights spills source 0 = 0 := by
  simp [baseline]

theorem baseline_add_singleton (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) (value : Value) :
    baseline costs weights spills source (missing + {value}) =
      baseline costs weights spills source missing + unitPrice costs weights spills value +
        if value ∈ source ∨ value ∈ missing then 0
        else directPrice costs weights spills value - unitPrice costs weights spills value := by
  by_cases hs : value ∈ source <;> by_cases hm : value ∈ missing <;>
    simp [baseline, Multiset.toFinset_add, Finset.sum_insert, hs, hm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem directPrice_of_free (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) (h : value.can_be_freely_generated) :
    directPrice costs weights spills value = (costs.push value).score weights := by
  cases value <;> simp_all [directPrice, Value.can_be_freely_generated]

end Shuffler.Optimality
