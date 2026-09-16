import Init.Data.List.Basic
import Mathlib.Data.Nat.Basic

abbrev Value := ℕ

abbrev Stack := List Value
abbrev Permutation (source : Stack) := Vector (Fin source.length) source.length

def List.swap
  {α : Type u} (xs : List α) (i j : ℕ)
  (hi : i < xs.length := by get_elem_tactic)
  (hj : j < xs.length := by get_elem_tactic)
  := (xs.set i xs[j]).set j xs[i]

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

def apply_permutation (source : Stack) (perm : Permutation source) : Stack :=
  List.foldl
    (λ res idx => res.set (perm[idx].val) source[idx])
    (List.range source.length)
    (List.finRange source.length)

def ApplyPermutation
  (source : Stack)
  (perm : List (Fin source.length))
  : Stack
  := perm.map (λ i => source[i])

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
      let top := current.length - 1
      -- if the top is out of place, we swap it into position
      if ht : perm[top] ≠ top
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
        let idx := top - perm[top]

        let stack' := current.swap (current.length - 1) (current.length - 1 - idx)
        let perm' := perm.swap top perm[top]

        have h1 : idx < current.length := by rw [hlen]; grind only [= Lean.Grind.toInt_fin]
        have h2 : 1 ≤ idx := by omega
        have h3 : idx < 17 := by omega
        let trace' := .Swap idx h1 h2 h3 trace

        go stack' perm' trace' (by dsimp[stack']; simp [List.swap, hlen])

      -- search for the shallowest out of place element
      else
        -- we make pos a subtype that carries a proof that pos is out of place.
        -- we need this later for the range proofs when generating the trace
        let pos : Option {i : Fin current.length // (perm[(i : ℕ)]'(hlen ▸ i.isLt) : ℕ) ≠ (i : ℕ)} :=
          (List.finRange current.length).foldl
            (λ p (i : Fin current.length) =>
              if h : (perm[(i : ℕ)]'(hlen ▸ i.isLt) : ℕ) ≠ (i : ℕ) then .some ⟨i, h⟩ else p)
            .none
        match pos with

        -- swap top with pos
        | some ⟨pos, hpos⟩ =>
          -- `pos` is misplaced but `top` is in place, so `pos ≠ top`
          -- `pos < top` by congruence on `perm[·]` (if `pos = top` then `perm[pos] = perm[top] = top = pos`).
          have hlt : (pos : ℕ) < top := by have := pos.isLt; grind
          let idx := current.length - 1 - pos
          let stack' := current.swap (current.length - 1) (current.length - 1 - idx)
          let perm' := perm.swap top pos

          let trace' := .Swap idx (by omega) (by omega) (by omega) trace
          go stack' perm' trace' (by dsimp[stack']; simp [List.swap, hlen])

        -- we're done
        | none => ⟨current, trace⟩


-- the stack returned by permute is always the result of applying the permutation perm to the source
theorem permute_applies_permutation
  (source : Stack)
  (perm : Permutation source)
  (hlo : source.length > 0)
  (hhi : source.length < 17) :
    (permute source perm hlo hhi).1 = apply_permutation source perm
  := sorry
