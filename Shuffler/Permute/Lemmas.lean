import Init.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.GroupTheory.Perm.Support

namespace Shuffler.Permute

namespace Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The number of out-of-place elements
-- other than `top`, then whether `top` itself is in place (1) or not (0).
-- Compared lexicographically.
def measure (perm : Equiv.Perm ι) (top : ι) : ℕ × ℕ :=
  ((perm.support.erase top).card, if perm top = top then 1 else 0)

-- When `top` is out of place, swapping it into place decreases the first component
-- of the measure
lemma measure_place_top_lt (perm : Equiv.Perm ι)
    (top : ι) (ht : perm top ≠ top) :
    (measure (perm * Equiv.swap top (perm top)) top).1 < (measure perm top).1 := by
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
  exact Finset.card_erase_lt_of_mem (by simp [ht])

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

-- A permutation cannot move just one position. If every position other than
-- `top` is fixed, `top` must be fixed too.
theorem measure_fst_eq_zero_iff (perm : Equiv.Perm ι) (top : ι) :
    (measure perm top).1 = 0 ↔ perm = 1 := by
  constructor
  · intro h
    have hzero : (perm.support.erase top).card = 0 := h
    have hcard : perm.support.card - 1 ≤ (perm.support.erase top).card :=
      Finset.pred_card_le_card_erase
    apply Equiv.Perm.card_support_le_one.mp
    omega
  · rintro rfl
    simp [measure]

-- The terminal measure identifies the identity permutation.
theorem measure_eq_terminal_iff (perm : Equiv.Perm ι) (top : ι) :
    measure perm top = (0, 1) ↔ perm = 1 := by
  constructor
  · intro h
    exact (measure_fst_eq_zero_iff perm top).mp (congrArg Prod.fst h)
  · rintro rfl
    simp [measure]

end Permutation

variable {α : Type*}

-- Apply a permutation to a list whose length is propositionally equal to the
-- permutation's domain size.
def apply_permutation' (current : List α) {n : ℕ} (perm : Equiv.Perm (Fin n))
    (hlen : current.length = n) : List α :=
  List.ofFn (fun k : Fin n => current[(perm.symm k).val]'(by have := (perm.symm k).isLt; omega))

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

-- Express a depth-based swap using the absolute positions in the permutation.
theorem apply_permutation'_swap_top (current : List α) {n : ℕ}
    (perm : Equiv.Perm (Fin n)) (hlen : current.length = n)
    (top : Fin n) (htop : top.val = n - 1) (pos : Fin n) :
    apply_permutation'
      (current.swap (current.length - 1) (current.length - 1 - pos.rev.val))
      (perm * Equiv.swap top pos) (by simp [hlen]) = apply_permutation' current perm hlen := by
  have hswap : current.swap (current.length - 1) (current.length - 1 - pos.rev.val)
      = current.swap top.val pos.val := by
    dsimp [Fin.rev]
    congr 1 <;> omega
  simpa only [hswap] using apply_permutation'_swap current perm hlen top pos

-- At the terminal measure, applying the remaining permutation does nothing.
theorem apply_permutation'_terminal (current : List α) {n : ℕ}
    (perm : Equiv.Perm (Fin n)) (hlen : current.length = n)
    (top : Fin n) (hterminal : Permutation.measure perm top = (0, 1)) :
    apply_permutation' current perm hlen = current := by
  rw [(Permutation.measure_eq_terminal_iff perm top).mp hterminal, apply_permutation'_one]

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

-- Swapping reachable positions leaves the support at unreachable positions unchanged.
theorem unreachable_mem_support_swap {n depth : ℕ}
    (perm : Equiv.Perm (Fin n)) (a b i : Fin n)
    (ha : a.rev.val ≤ depth) (hb : b.rev.val ≤ depth)
    (hi : depth < i.rev.val) :
    i ∈ (perm * Equiv.swap a b).support ↔ i ∈ perm.support := by
  have hia : i ≠ a := by rintro rfl; omega
  have hib : i ≠ b := by rintro rfl; omega
  simp only [Equiv.Perm.mem_support, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hia hib]

theorem all_swaps_reachable_swap_iff {n depth : ℕ}
    (perm : Equiv.Perm (Fin n)) (a b : Fin n)
    (ha : a.rev.val ≤ depth) (hb : b.rev.val ≤ depth) :
    (∀ i ∈ (perm * Equiv.swap a b).support, i.rev.val ≤ depth) ↔
      (∀ i ∈ perm.support, i.rev.val ≤ depth) := by
  constructor <;> intro h i hi <;> by_contra hdepth
  · exact hdepth (h i ((unreachable_mem_support_swap perm a b i ha hb
      (Nat.lt_of_not_ge hdepth)).mpr hi))
  · exact hdepth (h i ((unreachable_mem_support_swap perm a b i ha hb
      (Nat.lt_of_not_ge hdepth)).mp hi))

-- Transport a blocked result across a reachable swap; the result predicate
-- records the error independently of the remaining permutation.
theorem blocked_of_reachable_swap {n depth : ℕ} (perm : Equiv.Perm (Fin n))
    (a b : Fin n) (ha : a.rev.val ≤ depth) (hb : b.rev.val ≤ depth)
    {blocked : ℕ → Prop}
    (ih : ¬(∀ i ∈ (perm * Equiv.swap a b).support, i.rev.val ≤ depth) →
      ∃ x, blocked x ∧ 0 < x ∧ ∃ i ∈ (perm * Equiv.swap a b).support, i.rev.val = x + depth)
    (hnreach : ¬(∀ i ∈ perm.support, i.rev.val ≤ depth)) :
    ∃ x, blocked x ∧ 0 < x ∧ ∃ i ∈ perm.support, i.rev.val = x + depth := by
  obtain ⟨x, hresult, hx, i, hi, hidx⟩ := ih (fun hr =>
    hnreach ((all_swaps_reachable_swap_iff perm a b ha hb).mp hr))
  exact ⟨x, hresult, hx, i,
    (unreachable_mem_support_swap perm a b i ha hb (by omega)).mp hi, hidx⟩

end Shuffler.Permute
