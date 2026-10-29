module

public import Shuffler.Emission.Defs
public import Shuffler.Permute.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Factors

@[expose] public section

namespace Shuffler.Permute

open Emission

abbrev Permutation (source : Stack) := Equiv.Perm (Fin source.length)

namespace Permutation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Mathlib's cycle factors exclude fixed points.
def cyclesAwayFromTop (perm : Equiv.Perm ι) (top : ι) : Finset (Equiv.Perm ι) :=
  perm.cycleFactorsFinset.filter (fun cycle => cycle top = top)

-- A cycle containing the top contributes k - 1; every other cycle contributes k + 1.
def swapCount (perm : Equiv.Perm ι) (top : ι) : ℕ :=
  (perm.support.erase top).card + (cyclesAwayFromTop perm top).card

-- The minimum count when a swap can use any two positions.
def arbitrarySwapCount (perm : Equiv.Perm ι) : ℕ :=
  perm.support.card - perm.cycleFactorsFinset.card

end Permutation

-- permute applies a permutation to the working stack and updates its trace.
-- A blocked run returns the state after all preceding swaps.
-- TODO: Match C++ by reassigning destinations among equal values before processing
-- cycles. Keep positions already at a destination needed by their group, then
-- pair the remaining positions and destinations in ascending order.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:629-675.
def permute
  {source target : Stack} {spills : SpillSet}
  (initial : State source target spills)
  (perm : Permutation initial.stack)
  : Except ShuffleErr (Result source target spills)
  := if hne : 0 < initial.stack.length
  then go initial perm hne
  else .ok ⟨none, initial⟩
  where
    -- TODO: In both exchange branches, compare the selected value with the top
    -- before checking SWAP reach. For equal values, exchange their permutation
    -- destinations without changing the stack or emitting a swap, as C++ does.
    -- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:677-687.
    go (state : State source target spills) (perm : Permutation state.stack)
        (hne : state.stack.length > 0) :
        Except ShuffleErr (Result source target spills) :=
      let top : Fin state.stack.length := ⟨state.stack.length - 1, by omega⟩
      have htop : top.val = state.stack.length - 1 := rfl
      -- if the top is out of place, we swap it into position
      if ht : perm top ≠ top
      then
        let idx : ℕ := (perm top).rev.val
        if hdepth : idx > MAX_SWAP_DEPTH then
          state.blockSwapUnreachable (perm top)
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

          let stack' := state.stack.swap (state.stack.length - 1) (state.stack.length - 1 - idx)
          let perm' := perm * Equiv.swap top (perm top)

          have h1 : idx < state.stack.length := (perm top).rev.isLt
          have h2 : 1 ≤ idx := by
            -- we need the isLt proof of it
            have hlt := (perm top).isLt
            dsimp [idx, Fin.rev]
            omega
          have h3 : idx ≤ MAX_SWAP_DEPTH := by omega
          let trace' := .Swap idx h1 h2 h3 state.trace

          go {
            state with
            stack := stack'
            trace := trace'
            mapping := List.length_swap.symm ▸ state.mapping
          } (by simpa [Permutation, stack'] using perm')
            (List.length_swap.symm ▸ hne)

      -- search for the shallowest out of place element
      else
        -- we make pos a subtype that carries a proof that pos is out of place.
        -- we need this later for the range proofs when generating the trace
        let pos : Option {i : Fin state.stack.length // perm i ≠ i} :=
          (List.finRange state.stack.length).foldl
            (λ p (i : Fin state.stack.length) =>
              if h : perm i ≠ i then .some ⟨i, h⟩ else p)
            .none
        match pos with

        -- swap top with pos
        | some ⟨pos, hpos⟩ =>
          let idx : ℕ := pos.rev.val
          if hdepth : idx > MAX_SWAP_DEPTH then
            state.blockSwapUnreachable pos
          else

            -- `top` is a fixed point, so the out-of-place `pos` is strictly below it
            have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
            have hlt : (pos : ℕ) < top := by
              have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; omega
            let stack' := state.stack.swap (state.stack.length - 1) (state.stack.length - 1 - idx)
            let perm' := perm * Equiv.swap top pos

            have h1 : idx < state.stack.length := pos.rev.isLt
            have h2 : 1 ≤ idx := by dsimp [idx, Fin.rev]; omega
            have h3 : idx ≤ MAX_SWAP_DEPTH := by omega
            let trace' := .Swap idx h1 h2 h3 state.trace
            go {
              state with
              stack := stack'
              trace := trace'
              mapping := List.length_swap.symm ▸ state.mapping
            } (by simpa [Permutation, stack'] using perm')
              (List.length_swap.symm ▸ hne)

        -- we're done
        | none => .ok ⟨none, state⟩
    termination_by Permutation.measure perm ⟨state.stack.length - 1, by omega⟩
    decreasing_by
      · simp only [eq_mpr_eq_cast]
        rw [Permutation.measure_cast List.length_swap.symm _ hne]
        exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm _ ht)
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm _ pos (not_not.mp ht) hpos
        simp only [eq_mpr_eq_cast]
        rw [Permutation.measure_cast List.length_swap.symm _ hne]
        exact Prod.Lex.right' _ heq.le hlt

-- applies the permutation perm to the source stack via the inverse equivalence
-- every proper permutation has an inverse
def apply_permutation (source : Stack) (perm : Permutation source) : Stack :=
  List.ofFn (λ k => source[perm.symm k])

def all_swaps_reachable (perm : Permutation source) : Prop
  := ∀ i ∈ perm.support, i.rev.val ≤ MAX_SWAP_DEPTH

end Shuffler.Permute
