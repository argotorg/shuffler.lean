import Shuffler.Optimality.BirthPlacement.SourceLazy.Spec
import Shuffler.Optimality.BirthPlacement.SourceLazy.Cached
import Shuffler.Optimality.BirthPlacement.SourcePlan.Theorems

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

open Shuffler.Permute.Permutation Shuffler.Placement

structure State (plan : SourcePlan spills source target) (height : Nat) where
  source_le : source.length ≤ height
  height_le : height ≤ target.length
  remaining : Equiv.Perm (Fin target.length)
  above : ∀ index : Fin target.length, height ≤ index.val → remaining index = index
  deadlines : BirthDeadlines 16 remaining
  source_frozen : ∀ index : Fin target.length,
    index.val + 17 < source.length → remaining index = index
  frozen : ∀ index : Fin target.length, index.val + 16 < height →
    (plan.assignment * remaining⁻¹) index = index

variable {spills : SpillSet} {source target : Stack}
  {plan : SourcePlan spills source target} {height : Nat}

abbrev State.values (state : State plan height) : Stack :=
  prefixValues target (plan.assignment * state.remaining⁻¹) height

structure Result (plan : SourcePlan spills source target) (height : Nat)
    (state : State plan height) where
  built : BuiltTrace spills source state.values
    (plan.births.take (height - source.length) : Multiset Value)
  count : built.trace.swapCount = swapBound 16 source.length state.remaining
  events : traceEvents built.trace = plan.events.take (height - source.length)

def State.initial (plan : SourcePlan spills source target) : State plan target.length where
  source_le := plan.source_length
  height_le := le_refl _
  remaining := plan.assignment
  above := by intro index hi; have := index.isLt; omega
  deadlines := plan.deadlines
  source_frozen := plan.source_frozen
  frozen := by intro index _; simp

theorem State.values_length (state : State plan height) : state.values.length = height := by
  simp only [State.values, prefixValues_length, Nat.min_eq_left state.height_le]

theorem State.values_frozen (state : State plan height) :
    state.values.take (height - 16) = target.take (height - 16) := by
  apply List.ext_getElem
  · simp only [List.length_take, state.values_length]
    have := state.height_le
    omega
  · intro index hi hj
    have hic : index < height - 16 := by simp only [List.length_take, state.values_length] at hi; omega
    have hin : index < target.length := by have := state.height_le; omega
    have he := state.frozen ⟨index, hin⟩ (by change index + 16 < height; omega)
    simp only [State.values, prefixValues, birthWord, List.getElem_take, List.getElem_ofFn, he]
    rfl

-- Moving backwards across one birth changes only the reachable positions.
-- The supplied local step proves its own deadline and fixed-row facts.
def State.rewind (top : Fin target.length) (state : State plan (top.val + 1))
    (hsource : source.length ≤ top.val)
    (movement : Equiv.Perm (Fin target.length))
    (hreach : ∀ index ∈ movement.support, top.val ≤ index.val + 16)
    (habove : ∀ index : Fin target.length, top.val ≤ index.val →
      (movement⁻¹ * state.remaining) index = index)
    (hdeadline : BirthDeadlines 16 (movement⁻¹ * state.remaining)) : State plan top.val where
  source_le := hsource
  height_le := Nat.le_of_lt top.isLt
  remaining := cachedPermutation (movement⁻¹ * state.remaining)
  above := by simpa only [cachedPermutation_eq] using habove
  deadlines := by simpa only [cachedPermutation_eq] using hdeadline
  source_frozen := by
    rw [cachedPermutation_eq]
    intro index hi
    have hr := state.source_frozen index hi
    have hm : movement index = index := by
      apply Equiv.Perm.notMem_support.mp
      intro hh
      have := hreach index hh
      omega
    simp only [Equiv.Perm.mul_apply, hr]
    exact (Equiv.Perm.inv_eq_iff_eq.mpr hm.symm)
  frozen := by
    rw [cachedPermutation_eq]
    intro index hi
    have hm : movement index = index := by
      apply Equiv.Perm.notMem_support.mp
      intro hh
      have := hreach index hh
      omega
    simp only [mul_inv_rev, inv_inv, ← mul_assoc, Equiv.Perm.mul_apply, hm]
    exact state.frozen index (by omega)

end Shuffler.Optimality.BirthPlacement.SourceLazy
