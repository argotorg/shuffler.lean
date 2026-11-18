module

public import Mathlib.GroupTheory.Perm.Support

@[expose] public section

namespace Shuffler.Permute

namespace Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The number of out-of-place elements
-- other than `top`, then whether `top` itself is in place (1) or not (0).
-- Compared lexicographically.
def measure (perm : Equiv.Perm ι) (top : ι) : ℕ × ℕ :=
  ((perm.support.erase top).card, if perm top = top then 1 else 0)

theorem measure_cast {n m : ℕ} (h : n = m) (perm : Equiv.Perm (Fin n)) (hne : 0 < n) :
    measure (cast (congrArg (fun k => Equiv.Perm (Fin k)) h) perm) ⟨m - 1, by omega⟩ =
      measure perm ⟨n - 1, by omega⟩ := by
  subst m
  rfl

theorem mem_support_cast {n m : ℕ} (h : n = m) (perm : Equiv.Perm (Fin n)) (i : Fin m) :
    i ∈ (cast (congrArg (fun k => Equiv.Perm (Fin k)) h) perm).support ↔
      Fin.cast h.symm i ∈ perm.support := by
  subst m
  rfl

-- Placing the top fixes exactly one position below it.
lemma measure_place_top (perm : Equiv.Perm ι)
    (top : ι) (ht : perm top ≠ top) :
    (measure (perm * Equiv.swap top (perm top)) top).1 + 1 = (measure perm top).1 := by
  -- the swap puts `perm top` in place and leaves everyone else's status unchanged
  have hset : (perm * Equiv.swap top (perm top)).support.erase top
      = (perm.support.erase top).erase (perm top) := by
    ext x
    simp only [Finset.mem_erase, Equiv.Perm.mem_support, Equiv.Perm.mul_apply]
    cases eq_or_ne x top with
    | inl hx =>
      subst hx
      simp
    | inr hx =>
      cases eq_or_ne x (perm top) with
      | inl hx' =>
        subst hx'
        simp
      | inr hx' =>
        rw [Equiv.swap_apply_of_ne_of_ne hx hx']
        simp [hx, hx']
  simp only [measure, hset]
  exact Finset.card_erase_add_one (by simp [ht])

lemma measure_place_top_lt (perm : Equiv.Perm ι)
    (top : ι) (ht : perm top ≠ top) :
    (measure (perm * Equiv.swap top (perm top)) top).1 < (measure perm top).1 := by
  have := measure_place_top perm top ht
  omega

-- When `top` is in place, swapping it with an out-of-place `pos` keeps the
-- first component and puts `top` out of place, decreasing the second component
lemma measure_swap_pos_lt (perm : Equiv.Perm ι)
    (top pos : ι) (ht : perm top = top) (hpos : perm pos ≠ pos) :
    (measure (perm * Equiv.swap top pos) top).1 = (measure perm top).1 ∧
    (measure (perm * Equiv.swap top pos) top).2 < (measure perm top).2 := by
  -- the swap moves `top` out of place and leaves everyone else's status unchanged
  have hset : (perm * Equiv.swap top pos).support.erase top = perm.support.erase top := by
    ext x
    simp only [Finset.mem_erase, Equiv.Perm.mem_support, Equiv.Perm.mul_apply]
    cases eq_or_ne x top with
    | inl hx =>
      subst hx
      simp
    | inr hx =>
      cases eq_or_ne x pos with
      | inl hx' =>
        subst hx'
        simp [ht, hx, hpos, Ne.symm hx]
      | inr hx' =>
        rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  -- `top` is a fixed point and `perm` is injective, so `pos` can't map to it
  have : perm pos ≠ top := fun h => hpos (by rw [perm.injective (h.trans ht.symm)]; exact ht)
  simp [measure, hset, ht, this]

-- Exchanging the destinations of `pos` and `perm pos` puts `perm pos` in place.
lemma card_support_mul_swap_lt (perm : Equiv.Perm ι) (pos : ι) (hpos : perm pos ≠ pos) :
    (perm * Equiv.swap (perm pos) pos).support.card < perm.support.card := by
  have h := Equiv.Perm.card_support_swap_mul (f := perm⁻¹) (x := perm pos) (by simpa using hpos.symm)
  rwa [show perm⁻¹ (perm pos) = pos from perm.symm_apply_apply pos, ← Equiv.swap_inv, ← mul_inv_rev,
    Equiv.Perm.support_inv, Equiv.Perm.support_inv] at h

end Permutation

variable {α : Type*}

-- Apply a permutation to a list whose length is propositionally equal to the
-- permutation's domain size.
def apply_permutation' (current : List α) {n : ℕ} (perm : Equiv.Perm (Fin n))
    (hlen : current.length = n) : List α :=
  List.ofFn (fun k : Fin n => current[(perm.symm k).val]'(by have := (perm.symm k).isLt; omega))

theorem apply_permutation'_cast (current : List α) {n m : ℕ} (h : n = m)
    (perm : Equiv.Perm (Fin n)) (hlen : current.length = m) :
    apply_permutation' current (cast (congrArg (fun k => Equiv.Perm (Fin k)) h) perm) hlen =
      apply_permutation' current perm (hlen.trans h.symm) := by
  subst m
  rfl

theorem apply_permutation'_one (current : List α) {n : ℕ} (hlen : current.length = n) :
    apply_permutation' current (1 : Equiv.Perm (Fin n)) hlen = current := by
  apply List.ext_getElem <;> simp [apply_permutation', Equiv.Perm.one_def, hlen]

-- Swapping two entries of the list and composing the permutation with the same swap
-- leaves the applied result unchanged.
theorem apply_permutation'_swap (current : List α) {n : ℕ} (perm : Equiv.Perm (Fin n))
    (hlen : current.length = n) (a b : Fin n) :
    apply_permutation' (current.swap a.val b.val) (perm * Equiv.swap a b) (by simp [hlen])
      = apply_permutation' current perm hlen := by
  unfold apply_permutation'
  rw [List.ofFn_inj]
  funext k
  have hsymm : (perm * Equiv.swap a b).symm k = Equiv.swap a b (perm.symm k) := rfl
  simp only [hsymm]
  by_cases ha : perm.symm k = a
  · simp [ha, hlen]
  by_cases hb : perm.symm k = b
  · simp [hb, hlen]
  simp [Equiv.swap_apply_of_ne_of_ne ha hb, Fin.val_ne_of_ne ha, Fin.val_ne_of_ne hb]

-- If the linear search for an out-of-place element comes back empty, every element
-- of the searched list is a fixed point (and the accumulator was empty to begin with).
theorem foldl_find_out_of_place_none {n : ℕ} (perm : Equiv.Perm (Fin n)) (l : List (Fin n))
    (p : Option {i : Fin n // perm i ≠ i}) :
    l.foldl (fun p (i : Fin n) => if h : perm i ≠ i then some ⟨i, h⟩ else p) p = none →
      p = none ∧ ∀ i ∈ l, perm i = i := by
  induction l generalizing p with
  | nil => simp
  | cons x xs ih =>
    intro h
    obtain ⟨hp, hxs⟩ := ih _ h
    by_cases hx : perm x = x
    · exact ⟨by simpa [hx] using hp, by simpa [hx] using hxs⟩
    · simp [hx] at hp

theorem foldl_find_out_of_place_eq_one {n : ℕ} (perm : Equiv.Perm (Fin n))
    (h : (List.finRange n).foldl
      (fun (p : Option {i // perm i ≠ i}) i => if h : perm i ≠ i then some ⟨i, h⟩ else p)
      none = none) :
    perm = 1 :=
  Equiv.ext fun i => (foldl_find_out_of_place_none perm _ none h).2 i (List.mem_finRange i)

end Shuffler.Permute
