import Mathlib.GroupTheory.Perm.Cycle.Basic

open Equiv
namespace Shuffler.BuildBottomUp

variable {α : Type*} [DecidableEq α]

-- Fix c by exchanging its destination with the position currently assigned to c.
def deleteCyclePoint (p : Equiv.Perm α) (c : α) : Equiv.Perm α :=
  p * Equiv.swap c (p.symm c)

@[simp] theorem deleteCyclePoint_apply_self (p : Equiv.Perm α) (c : α) :
    deleteCyclePoint p c c = c := by
  simp [deleteCyclePoint, Equiv.Perm.mul_apply]

theorem deleteCyclePoint_apply (p : Equiv.Perm α) (c x : α) :
    deleteCyclePoint p c x = if x = c then c else if p x = c then p c else p x := by
  by_cases hx : x = c
  · subst x
    simp
  by_cases hpx : p x = c
  · have hpre : x = p.symm c := by simpa using congrArg p.symm hpx
    rw [ite_eq_right hx, ite_eq_left hpx]
    simp only [deleteCyclePoint, Equiv.Perm.mul_apply, hpre, Equiv.swap_apply_right]
  · have hpre : x ≠ p.symm c := by
      intro he
      apply hpx
      rw [he, p.apply_symm_apply]
    rw [ite_eq_right hx, ite_eq_right hpx]
    simp only [deleteCyclePoint, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx hpre]

omit [DecidableEq α] in
theorem sameCycle_map_of_step [Finite α] {β : Type*} (p : Equiv.Perm α)
    (q : Equiv.Perm β) (r : α → β)
    (hstep : ∀ x, q.SameCycle (r x) (r (p x)))
    {x y : α} (h : p.SameCycle x y) : q.SameCycle (r x) (r y) := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simpa using Equiv.Perm.SameCycle.refl q (r x)
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (hstep ((p ^ k) x))

theorem deleteCyclePoint_sameCycle_imp [Finite α] (p : Equiv.Perm α) (c : α)
    {x y : α} (h : (deleteCyclePoint p c).SameCycle x y) : p.SameCycle x y := by
  apply sameCycle_map_of_step (deleteCyclePoint p c) p id _ h
  intro i
  simp only [id_eq, deleteCyclePoint_apply]
  split_ifs with hi hpi
  · subst i
    exact Equiv.Perm.SameCycle.refl p c
  · exact (show p.SameCycle i c from hpi ▸ (Equiv.Perm.SameCycle.refl p i).apply_right).trans
      ((Equiv.Perm.SameCycle.refl p c).apply_right)
  · exact (Equiv.Perm.SameCycle.refl p i).apply_right

-- Removing one point preserves cycle membership between all other points.
theorem deleteCyclePoint_sameCycle_iff [Finite α] (p : Equiv.Perm α) (c : α)
    {x y : α} (hx : x ≠ c) (hy : y ≠ c) :
    (deleteCyclePoint p c).SameCycle x y ↔ p.SameCycle x y := by
  refine ⟨deleteCyclePoint_sameCycle_imp p c, ?_⟩
  intro h
  let r : α → α := fun i => if i = c then p c else i
  have hstep : ∀ i, (deleteCyclePoint p c).SameCycle (r i) (r (p i)) := by
    intro i
    by_cases hi : i = c
    · subst i
      simp [r, Equiv.Perm.SameCycle.rfl]
    by_cases hpi : p i = c
    · have h := (Equiv.Perm.SameCycle.refl (deleteCyclePoint p c) i).apply_right
      simpa [r, hi, hpi, deleteCyclePoint_apply] using h
    · have h := (Equiv.Perm.SameCycle.refl (deleteCyclePoint p c) i).apply_right
      simpa [r, hi, hpi, deleteCyclePoint_apply] using h
  simpa [r, hx, hy] using sameCycle_map_of_step p (deleteCyclePoint p c) r hstep h

-- q fixes the processed prefix and retains the original cycle relation elsewhere.
structure ContractsCycles {m : Nat} (p q : Equiv.Perm (Fin m)) (c : Nat) : Prop where
  fixed : ∀ i, i.val < c → q i = i
  sameCycle : ∀ i j, c ≤ i.val → c ≤ j.val → (q.SameCycle i j ↔ p.SameCycle i j)

theorem ContractsCycles.initial {m : Nat} (p : Equiv.Perm (Fin m)) :
    ContractsCycles p p 0 where
  fixed := by intro i hi; omega
  sameCycle := by intros; rfl

theorem ContractsCycles.step {m c : Nat} {p q : Equiv.Perm (Fin m)}
    (h : ContractsCycles p q c) (hc : c < m) :
    ContractsCycles p (deleteCyclePoint q ⟨c,hc⟩) (c+1) where
  fixed := by
    intro i hi
    by_cases hic : i.val < c
    · have hfix := h.fixed i hic
      have hne : i ≠ ⟨c,hc⟩ := by intro he; have := congrArg Fin.val he; simp_all
      simp [deleteCyclePoint_apply, hfix, hne]
    · have he : i = ⟨c,hc⟩ := by apply Fin.ext; change i.val = c; omega
      subst i
      simp
  sameCycle := by
    intro i j hi hj
    have hni : i ≠ ⟨c,hc⟩ := by intro he; have := congrArg Fin.val he; simp_all
    have hnj : j ≠ ⟨c,hc⟩ := by intro he; have := congrArg Fin.val he; simp_all
    rw [deleteCyclePoint_sameCycle_iff q _ hni hnj]
    exact h.sameCycle i j (by omega) (by omega)

theorem ContractsCycles.retained {m c : Nat} {p q : Equiv.Perm (Fin m)}
    (h : ContractsCycles p q c) {i : Fin m} (hi : c ≤ i.val) : c ≤ (q i).val := by
  by_contra hn
  have hfix := h.fixed (q i) (by omega)
  have he : q i = i := q.injective hfix
  rw [he] at hn
  contradiction

theorem ContractsCycles.fixed_iff {m c : Nat} {p q : Equiv.Perm (Fin m)}
    (h : ContractsCycles p q c) {i : Fin m} (hi : c ≤ i.val) :
    q i = i ↔ ∀ j, c ≤ j.val → p.SameCycle i j → i = j := by
  constructor
  · intro hfix j hj hcycle
    exact ((h.sameCycle i j hi hj).mpr hcycle).eq_of_left hfix
  · intro hall
    exact (hall (q i) (h.retained hi)
      ((h.sameCycle i (q i) hi (h.retained hi)).mp (Equiv.Perm.SameCycle.refl q i).apply_right)).symm

theorem ContractsCycles.step_of_apply {m c : Nat} {p q : Equiv.Perm (Fin m)}
    (h : ContractsCycles p q c) (hc : c < m) (j : Fin m) (hj : q j = ⟨c,hc⟩) :
    ContractsCycles p (q * Equiv.swap ⟨c,hc⟩ j) (c+1) := by
  have he : j = q.symm ⟨c,hc⟩ := by simpa using congrArg q.symm hj
  simpa [deleteCyclePoint, he] using h.step hc

-- The terminal swap condition depends only on cycles of the original permutation.
theorem ContractsCycles.fixed_below_iff {m c d : Nat} {p q : Equiv.Perm (Fin m)}
    (h : ContractsCycles p q c) :
    (∀ i, i.val < d → q i = i) ↔
      ∀ i j, c ≤ i.val → i.val < d → c ≤ j.val → p.SameCycle i j → i = j := by
  constructor
  · intro hall i j hi hid hj hcycle
    exact (h.fixed_iff hi).mp (hall i hid) j hj hcycle
  · intro hall i hid
    by_cases hi : c ≤ i.val
    · exact (h.fixed_iff hi).mpr (fun j hj hcycle => hall i j hi hid hj hcycle)
    · exact h.fixed i (by omega)

end Shuffler.BuildBottomUp
