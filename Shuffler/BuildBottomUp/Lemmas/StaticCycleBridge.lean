import Shuffler.BuildBottomUp.Lemmas.StaticPermutation
import Shuffler.BuildBottomUp.Lemmas.StaticCycles

namespace Shuffler.BuildBottomUp.Success

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

theorem cyclesReady_iff (initial : State source target spills) (h : initial.Valid) (cursor : Nat) :
    CyclesReady initial cursor ↔
      ∀ i j : Fin target.length, cursor ≤ i.val →
        i.val < target.length - (MAX_SWAP_DEPTH + 1) → cursor ≤ j.val →
        (completedPermutation initial h).SameCycle i j → i = j := by
  constructor
  · intro hs i j hi hid hj hc
    obtain ⟨k, hk, he⟩ := (sameCycle_iff_bounded_iterate _ i j).mp hc
    have hv := completedPermutation_iterate_val initial h i k
    rw [he] at hv
    have hr := hs i.val hi hid k hk
    rw [← hv] at hr
    apply Fin.ext
    omega
  · intro hs i hi hid k hk
    have him : i < target.length := by omega
    let pos : Fin target.length := ⟨i, him⟩
    let next : Fin target.length :=
      (completedPermutation initial h : Fin target.length → Fin target.length)^[k] pos
    have hv : next.val = (completedNext initial)^[k] i :=
      completedPermutation_iterate_val initial h pos k
    by_cases hn : next.val < cursor
    · exact Or.inl (hv ▸ hn)
    · have hc : (completedPermutation initial h).SameCycle pos next :=
        (sameCycle_iff_bounded_iterate _ pos next).mpr ⟨k, hk, rfl⟩
      have he := hs pos next hi hid (by omega) hc
      exact Or.inr (hv.symm.trans (congrArg Fin.val he).symm)

end Shuffler.BuildBottomUp.Success
