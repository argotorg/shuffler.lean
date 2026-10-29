module

public import Shuffler.BuildBottomUp.Lemmas.StaticPermutation

@[expose] public section

namespace Shuffler.Emission.Success

theorem completedPermutation_iterate_val (initial : State source target spills) (h : initial.Valid)
    (i : Fin target.length) (k : Nat) :
    (((completedPermutation initial h : Fin target.length → Fin target.length)^[k]) i).val =
      (completedNext initial)^[k] i.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', completedPermutation_val, ih]

theorem sameCycle_iff_bounded_iterate {m : Nat} (p : Equiv.Perm (Fin m)) (i j : Fin m) :
    p.SameCycle i j ↔ ∃ k < m, (p : Fin m → Fin m)^[k] i = j := by
  simp only [Equiv.Perm.iterate_eq_pow]
  constructor
  · intro hc
    by_cases hi : i ∈ p.support
    · obtain ⟨k, hk, he⟩ := hc.exists_pow_eq_of_mem_support hi
      exact ⟨k, lt_of_lt_of_le hk (by simpa using Finset.card_le_univ (p.cycleOf i).support), he⟩
    · have he : p i = i := Equiv.Perm.notMem_support.mp hi
      exact ⟨0, by have := i.isLt; omega, by simpa using hc.eq_of_left he⟩
  · rintro ⟨k, _, he⟩
    exact ⟨(k : Int), by simpa using he⟩

end Shuffler.Emission.Success
