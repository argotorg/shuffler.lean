import Init.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.GroupTheory.Perm.Support

abbrev Value := ℕ

abbrev Stack := List Value
abbrev Permutation (source : Stack) := Equiv.Perm (Fin source.length)

inductive Trace : Stack → Stack → Type where
  | Lit : (s : Stack) → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev.swap (prev.length - 1) (prev.length - 1 - idx))

def Source : Stack := [0, 1, 2, 3]
def Target : Stack := [0, 3, 2, 1]
def TraceLitProducesExactStack : Trace Source Source := Trace.Lit Source
def Swap2Swaps2 : Trace Source Target := Trace.Swap 2
  (by dsimp[Source]; simp) (by simp) (by simp) (Trace.Lit Source)

-- applies the permutation perm to the source stack via the inverse equivalence
-- every proper permutation has an inverse
def apply_permutation (source : Stack) (perm : Permutation source) : Stack :=
  List.ofFn (λ k => source[perm.symm k])

-- swap offsets 1 and 3
def swap13 : Permutation Source := Equiv.swap (1 : Fin 4) (3 : Fin 4)
example : apply_permutation Source swap13 = [0, 3, 2, 1] := by rfl


-- Termination measure for `permute.go`: the number of out-of-place elements
-- other than `top`, then whether `top` itself is in place (1) or not (0).
-- Compared lexicographically.
def Permutation.measure {source : Stack} (perm : Permutation source) (top : Fin source.length) : ℕ×ℕ :=
  ((perm.support.erase top).card, if perm top = top then 1 else 0)

-- When `top` is out of place, swapping it into place decreases the first component
-- of the measure
theorem Permutation.measure_place_top_lt {source : Stack} (perm : Permutation source)
    (top : Fin source.length) (ht : perm top ≠ top) :
    ((perm * Equiv.swap top (perm top)).measure top).1 < (perm.measure top).1 := by
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
  simp only [Permutation.measure, hset]
  exact Finset.card_erase_lt_of_mem (by simp [ht])

-- When `top` is in place, swapping it with an out-of-place `pos` keeps the
-- first component and puts `top` out of place, decreasing the second component
theorem Permutation.measure_swap_pos_lt {source : Stack} (perm : Permutation source)
    (top pos : Fin source.length) (ht : perm top = top) (hpos : perm pos ≠ pos) :
    ((perm * Equiv.swap top pos).measure top).1 = (perm.measure top).1 ∧
    ((perm * Equiv.swap top pos).measure top).2 < (perm.measure top).2 := by
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
  simp [Permutation.measure, hset, ht, this]

-- permute takes a stack and a permutation, and returns the series of swap
-- operations required to transform the source into the result of applying the
-- permutation to it.
def permute
  (source : Stack)
  (perm : Permutation source)
  (hlo: source.length > 0)
  (hhi : source.length < 17)
  : (result : Stack) × Trace source result
  := go source perm (.Lit source) (by simp)
  where
    go (current : Stack) (perm : Permutation source) (trace : Trace source current) (hlen : current.length = source.length) : (result : Stack) × Trace source result :=
      let top : Fin source.length := ⟨source.length - 1, by omega⟩
      have htop : top.val = source.length - 1 := rfl
      -- if the top is out of place, we swap it into position
      if ht : perm top ≠ top
      then
        -- We want to swap the top element into position `perm[top]`. But `Trace.Swap`
        -- is parameterised by depth below the top, not an absolute index: it swaps
        -- position `len-1` with position `len-1-idx`. So we convert the target
        -- absolute position into a depth.
        --
        --   position:  0  1  ...  perm[top]  ...........  top = len-1
        --                          └─────────── idx ──────────┘        idx = depth below top
        --
        --   Trace.Swap idx  swaps  (len-1)  with  (len-1) - idx
        --   want that lower position to be perm[top]:
        --       (len-1) - idx = perm[top]  ⟹  idx = (len-1) - perm[top] = top - perm[top]

        -- Fins have modulo arithmetic, nats don't
        let idx : ℕ := top.val - (perm top).val

        let stack' := current.swap (current.length - 1) (current.length - 1 - idx)
        let perm' := perm * Equiv.swap top (perm top)

        have h1 : idx < current.length := by have := (perm top).isLt; omega
        have h2 : 1 ≤ idx := by
          -- we need the isLt proof of it
          have hlt := (perm top).isLt
          omega
        have h3 : idx < 17 := by omega
        let trace' := .Swap idx h1 h2 h3 trace

        go stack' perm' trace' (by dsimp[stack']; simp [hlen])

      -- search for the shallowest out of place element
      else
        -- we make pos a subtype that carries a proof that pos is out of place.
        -- we need this later for the range proofs when generating the trace
        let pos : Option {i : Fin source.length // perm i ≠ i} :=
          (List.finRange source.length).foldl
            (λ p (i : Fin source.length) =>
              if h : perm i ≠ i then .some ⟨i, h⟩ else p)
            .none
        match pos with

        -- swap top with pos
        | some ⟨pos, hpos⟩ =>

          -- `top` is a fixed point, so the out-of-place `pos` is strictly below it
          have hne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
          have hlt : (pos : ℕ) < top := by
            have := pos.isLt; have := Fin.val_ne_of_ne hne; omega
          let idx := current.length - 1 - pos
          let stack' := current.swap (current.length - 1) (current.length - 1 - idx)
          let perm' := perm * Equiv.swap top pos

          let trace' := .Swap idx (by omega) (by omega) (by omega) trace
          go stack' perm' trace' (by dsimp[stack']; simp [hlen])

        -- we're done
        | none => ⟨current, trace⟩
    termination_by Permutation.measure perm ⟨source.length - 1, by omega⟩
    decreasing_by
      · exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm _ ht)
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm _ pos (not_not.mp ht) hpos
        exact Prod.Lex.right' _ heq.le hlt



-- `apply_permutation` generalised to a stack whose length is merely propositionally
-- equal to the permutation's domain size.  `permute.go` needs this because `current`
-- is not syntactically `source`.
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

-- Invariant of the recursion: the stack `go` returns is the remaining permutation
-- applied to the current stack.
theorem permute_go_spec (source : Stack) (hlo : source.length > 0) (hhi : source.length < 17)
    (current : Stack) (perm : Permutation source) (trace : Trace source current)
    (hlen : current.length = source.length) :
    (permute.go source hlo hhi current perm trace hlen).1 = apply_permutation' current perm hlen := by
  fun_induction permute.go with
  | case1 current perm trace hlen top htop ht idx stack' perm' h1 h2 h3 trace' ih =>
    refine ih.trans ?_
    have e1 : current.length - 1 = top.val := by omega
    have e2 : top.val - idx = (perm top).val := by
      have := (perm top).isLt
      omega
    simpa only [stack', perm', e2, e1] using
      apply_permutation'_swap current perm hlen top (perm top)
  | case2 current perm trace hlen top htop ht pos pos1 hpos hposeq hne hlt idx stack' perm' trace' ih =>
    refine ih.trans ?_
    have e1 : current.length - 1 = top.val := by omega
    have e2 : top.val - idx = pos1.val := by
      have := pos1.isLt
      omega
    simpa only [stack', perm', e2, e1] using
      apply_permutation'_swap current perm hlen top pos1
  | case3 current perm trace hlen top htop ht pos hnone =>
    have hperm : perm = Equiv.refl _ := Equiv.ext fun i =>
      (foldl_find_out_of_place_none perm _ none hnone).2 i (List.mem_finRange i)
    apply List.ext_getElem <;> simp [apply_permutation', hlen, hperm]

-- the stack returned by permute is always the result of applying the permutation perm to the source
theorem permute_applies_permutation
  (source : Stack)
  (perm : Permutation source)
  (hlo : source.length > 0)
  (hhi : source.length < 17) :
    (permute source perm hlo hhi).1 = apply_permutation source perm :=
  permute_go_spec source hlo hhi source perm (.Lit source) rfl
