import Shuffler.Permute.Lemmas
import Data.Finset.Max

namespace Shuffler.Permute

abbrev Value := ℕ

abbrev Stack := List Value
abbrev Permutation (source : Stack) := Equiv.Perm (Fin source.length)

def MAX_SWAP_DEPTH := 16

inductive Trace : Stack → Stack → Type where
  | Lit : (s : Stack) → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev.swap (prev.length - 1) (prev.length - 1 - idx))

inductive PermuteErr : Type where
  | Blocked : ℕ → PermuteErr

-- permute takes a stack and a permutation, and returns the series of swap
-- operations required to transform the source into the result of applying the
-- permutation to it.
def permute
  (source : Stack)
  (perm : Permutation source)
  : Except PermuteErr ((result : Stack) × Trace source result)
  := match source with
  | [] => .ok ⟨[], .Lit []⟩
  | _ => go source perm (.Lit source) (by sorry) (by simp)
  where
    go (current : Stack) (perm : Permutation source) (trace : Trace source current) (hne : source.length > 0) (hlen : current.length = source.length) : Except PermuteErr ((result : Stack) × Trace source result) :=
      let top : Fin source.length := ⟨source.length - 1, by omega⟩
      have htop : top.val = source.length - 1 := rfl
      -- if the top is out of place, we swap it into position
      if ht : perm top ≠ top
      then
        let idx : ℕ := (perm top).rev.val
        if hdepth : idx > MAX_SWAP_DEPTH then .error (.Blocked (idx - MAX_SWAP_DEPTH))
        else
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

          let stack' := current.swap (current.length - 1) (current.length - 1 - idx)
          let perm' := perm * Equiv.swap top (perm top)

          have h1 : idx < current.length := by simpa [idx, hlen] using (perm top).rev.isLt
          have h2 : 1 ≤ idx := by
            -- we need the isLt proof of it
            have hlt := (perm top).isLt
            dsimp [idx, Fin.rev]
            omega
          have h3 : idx < 17 := by unfold MAX_SWAP_DEPTH at hdepth; omega
          let trace' := .Swap idx h1 h2 h3 trace

          go stack' perm' trace' (by sorry) (by dsimp[stack']; simp [hlen])

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
          let idx : ℕ := pos.rev.val
          if hdepth : idx > MAX_SWAP_DEPTH then .error (.Blocked (idx - MAX_SWAP_DEPTH))
          else

            -- `top` is a fixed point, so the out-of-place `pos` is strictly below it
            have hne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
            have hlt : (pos : ℕ) < top := by
              have := pos.isLt; have := Fin.val_ne_of_ne hne; omega
            let stack' := current.swap (current.length - 1) (current.length - 1 - idx)
            let perm' := perm * Equiv.swap top pos

            have h1 : idx < current.length := by simpa [idx, hlen] using pos.rev.isLt
            have h2 : 1 ≤ idx := by dsimp [idx, Fin.rev]; omega
            have h3 : idx < 17 := by unfold MAX_SWAP_DEPTH at hdepth; omega
            let trace' := .Swap idx h1 h2 h3 trace
            go stack' perm' trace' (by sorry) (by dsimp[stack']; simp [hlen])

        -- we're done
        | none => .ok ⟨current, trace⟩
    termination_by Permutation.measure perm ⟨source.length - 1, by omega⟩
    decreasing_by
      · exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm _ ht)
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm _ pos (not_not.mp ht) hpos
        exact Prod.Lex.right' _ heq.le hlt

-- applies the permutation perm to the source stack via the inverse equivalence
-- every proper permutation has an inverse
def apply_permutation (source : Stack) (perm : Permutation source) : Stack :=
  List.ofFn (λ k => source[perm.symm k])

def all_swaps_reachable (perm : Permutation source) : Prop
  := ∀ i ∈ perm.support, i.rev.val ≤ MAX_SWAP_DEPTH

theorem permute_blocks_unreachable
  (source : Stack)
  (perm : Permutation source)
  (hnreachable : ¬(all_swaps_reachable perm)
  : permute source perm = .error (.Blocked x)
    ∧ x > 0
    ∧ x + MAX_SWAP_DEPTH ∈ perm.support
      := by sorry

-- The induction principle for `permute.go` follows its two recursive branches
-- and its terminal branch. Each swap preserves the applied permutation.
theorem permute_applies_permutation_reachable
  (source : Stack)
  (perm : Permutation source)
  (hreachable : all_swaps_reachable perm)
  : permute source perm = .ok ⟨res, _⟩ ∧ res = apply_permutation source perm
    := by
      change (permute.go source hlo hhi source perm (.Lit source) rfl).1
        = apply_permutation' source perm rfl
      apply permute.go.induct source hlo hhi
        (motive := fun current remaining trace hlen =>
          (permute.go source hlo hhi current remaining trace hlen).1
            = apply_permutation' current remaining hlen)
      · intro current perm trace hlen top htop ht idx stack' perm' h1 h2 h3 trace' ih
        rw [permute.go.eq_1, dite_eq_left ht, ih]
        simpa only [stack', perm', idx, hlen, htop,
          Nat.sub_sub_self (Nat.le_sub_one_of_lt (perm top).isLt)] using
          apply_permutation'_swap current perm hlen top (perm top)
      · intro current perm trace hlen top htop ht search pos hpos hsearch hne hlt idx stack' perm' trace' ih
        dsimp only [search] at hsearch
        rw [permute.go.eq_1, dite_eq_right ht, hsearch, ih]
        simpa only [stack', perm', idx, hlen, htop,
          Nat.sub_sub_self (Nat.le_sub_one_of_lt pos.isLt)] using
          apply_permutation'_swap current perm hlen top pos
      · intro current perm trace hlen top htop ht search hsearch
        dsimp only [search] at hsearch
        rw [permute.go.eq_1, dite_eq_right ht, hsearch]
        have hperm : perm = 1 := Equiv.ext fun i =>
          (foldl_find_out_of_place_none perm _ none hsearch).2 i (List.mem_finRange i)
        simpa only [hperm] using (apply_permutation'_one current hlen).symm

end Shuffler.Permute
