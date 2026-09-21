import Shuffler.Permute.Defs

namespace Shuffler.Permute

-- A permutation cannot move just one position. If every position other than
-- `top` is fixed, `top` must be fixed too.
theorem Permutation.measure_fst_eq_zero_iff {source : Stack}
    (perm : Permutation source) (top : Fin source.length) :
    (perm.measure top).1 = 0 ↔ perm = 1 := by
  constructor
  · intro h
    have hzero : (perm.support.erase top).card = 0 := h
    have hcard : perm.support.card - 1 ≤ (perm.support.erase top).card :=
      Finset.pred_card_le_card_erase
    apply Equiv.Perm.card_support_le_one.mp
    omega
  · rintro rfl
    simp [Permutation.measure]

-- The terminal measure identifies the identity permutation.
theorem Permutation.measure_eq_terminal_iff {source : Stack}
    (perm : Permutation source) (top : Fin source.length) :
    perm.measure top = (0, 1) ↔ perm = 1 := by
  constructor
  · intro h
    exact (Permutation.measure_fst_eq_zero_iff perm top).mp (congrArg Prod.fst h)
  · rintro rfl
    simp [Permutation.measure]

-- Apply a permutation to a stack whose length is propositionally equal to the
-- permutation's domain size. The invariant for `permute.go` needs this because
-- `current` is not syntactically `source`.
def apply_permutation' (current : Stack) {n : ℕ} (perm : Equiv.Perm (Fin n))
    (hlen : current.length = n) : Stack :=
  List.ofFn (fun k : Fin n => current[(perm.symm k).val]'(by have := (perm.symm k).isLt; omega))

-- Swapping two entries of the stack and composing the permutation with the same swap
-- leaves the applied result unchanged.
theorem apply_permutation'_swap (current : Stack) {n : ℕ} (perm : Equiv.Perm (Fin n))
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

-- At the terminal measure, applying the remaining permutation does nothing.
theorem apply_permutation'_terminal (current : Stack) {source : Stack}
    (perm : Permutation source) (hlen : current.length = source.length)
    (top : Fin source.length) (hterminal : perm.measure top = (0, 1)) :
    apply_permutation' current perm hlen = current := by
  have hperm : perm = Equiv.refl _ :=
    (Permutation.measure_eq_terminal_iff perm top).mp hterminal
  apply List.ext_getElem <;> simp [apply_permutation', hlen, hperm]

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

-- A proposition about one unfolding of the original recursive function.
inductive permute.Step (source : Stack) (hlo : source.length > 0)
    (hhi : source.length < 17) (current : Stack) (perm : Permutation source)
    (trace : Trace source current) (hlen : current.length = source.length) : Prop where
  | done
      (terminal : perm.measure ⟨source.length - 1, by omega⟩ = (0, 1))
      (returns : permute.go source hlo hhi current perm trace hlen = ⟨current, trace⟩)
  | more (next : Stack) (remaining : Permutation source) (nextTrace : Trace source next)
      (nextLength : next.length = source.length)
      (preserves : apply_permutation' next remaining nextLength
        = apply_permutation' current perm hlen)
      (decreases : Prod.Lex Nat.lt Nat.lt
        (remaining.measure ⟨source.length - 1, by omega⟩)
        (perm.measure ⟨source.length - 1, by omega⟩))
      (recurses : permute.go source hlo hhi current perm trace hlen
        = permute.go source hlo hhi next remaining nextTrace nextLength)

-- This lemma alone unfolds go to establish the step contract.
theorem permute_go_step (source : Stack) (hlo : source.length > 0) (hhi : source.length < 17)
    (current : Stack) (perm : Permutation source) (trace : Trace source current)
    (hlen : current.length = source.length) :
    permute.Step source hlo hhi current perm trace hlen := by
  let top : Fin source.length := ⟨source.length - 1, by omega⟩
  have htop : top.val = source.length - 1 := rfl
  have e1 : current.length - 1 = top.val := by omega
  have hswap (pos : Fin source.length) (idx : ℕ) (hidx : top.val - idx = pos.val) :
      apply_permutation' (current.swap (current.length - 1) (current.length - 1 - idx))
        (perm * Equiv.swap top pos) (by simp [hlen]) = apply_permutation' current perm hlen := by
    simpa only [e1, hidx] using apply_permutation'_swap current perm hlen top pos
  -- The equation determines the recursive call's stack, permutation and trace.
  have hgo := permute.go.eq_1 source hlo hhi current perm trace hlen
  split at hgo
  next ht =>
    refine .more _ _ _ _ ?_ ?_ hgo
    · apply hswap
      have := (perm top).isLt
      omega
    · exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm top ht)
  next ht =>
    dsimp only at hgo
    split at hgo
    next pos hpos hsearch =>
      refine .more _ _ _ _ ?_ ?_ hgo
      · apply hswap
        have := pos.isLt
        omega
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm top pos (not_not.mp ht) hpos
        exact Prod.Lex.right' _ heq.le hlt
    next hsearch =>
      refine .done ?_ hgo
      apply (Permutation.measure_eq_terminal_iff perm top).mpr
      exact Equiv.ext fun i =>
        (foldl_find_out_of_place_none perm _ none hsearch).2 i (List.mem_finRange i)

-- Well-founded induction uses only the step contract: either the remaining
-- permutation is identity, or the next state preserves the target and decreases
-- the measure.
theorem permute_go_spec (source : Stack) (hlo : source.length > 0)
    (hhi : source.length < 17) (current : Stack) (perm : Permutation source)
    (trace : Trace source current) (hlen : current.length = source.length) :
    (permute.go source hlo hhi current perm trace hlen).1
      = apply_permutation' current perm hlen := by
  cases permute_go_step source hlo hhi current perm trace hlen with
  | done terminal returns =>
    rw [returns]
    exact (apply_permutation'_terminal current perm hlen _ terminal).symm
  | more next remaining nextTrace nextLength preserves decreases recurses =>
    rw [recurses]
    exact (permute_go_spec source hlo hhi next remaining nextTrace nextLength).trans preserves
termination_by perm.measure ⟨source.length - 1, by omega⟩
decreasing_by exact decreases

end Shuffler.Permute
