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

-- permute applies a permutation to the working stack and updates its mapping and trace.
-- A blocked run returns the state after all preceding swaps.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:629-715.
def permute
  {source target : Stack} {spills : SpillSet}
  (initial : State source target spills)
  (perm : Permutation initial.stack)
  : Except ShuffleErr (Result source target spills)
  := do
    let mut perm := perm

    perm := minimizePermutationSupport initial.stack perm 0
    perm := minimizeCyclesWithoutTop initial.stack perm

    if hne : 0 < initial.stack.length then go initial perm hne
    else return ⟨none, initial⟩
  where
    -- Equal slots are interchangeable, so two equal slots may exchange their destinations.
    -- A slot already holding its target value stays; the slot bound for its offset takes over
    -- its destination
    minimizePermutationSupport (stack : Stack) (perm : Permutation stack) (position : ℕ) : Permutation stack :=
      if h : position < stack.length then
        let destination := perm ⟨position, h⟩
        if hd : destination ≠ ⟨position, h⟩ ∧ stack[destination] = stack[position] then
          minimizePermutationSupport stack (perm * Equiv.swap destination ⟨position, h⟩) position
        else
          minimizePermutationSupport stack perm (position + 1)
      else
        perm
    termination_by stack.length - position + perm.support.card
    decreasing_by
      · have := Permutation.card_support_mul_swap_lt perm _ hd.1
        omega
      · omega

    -- Join all cycles that share a value by exchanging the destinations of equal slots. Each join saves the swap
    -- that enters a cycle without the top. The top takes part even when it stays in place.
    minimizeCyclesWithoutTop (stack : Stack) (perm : Permutation stack) : Permutation stack := Id.run do
      let mut perm := perm
      for a in List.finRange stack.length do
        if perm a ≠ a then
          for b in List.finRange stack.length do
            if a < b ∧ stack[a] = stack[b] ∧ (if perm b = b then b.val = stack.length - 1 else ¬ perm.SameCycle a b) then
              perm := perm * Equiv.swap a b
      return perm

    go (state : State source target spills) (perm : Permutation state.stack)
        (hne : state.stack.length > 0) :
        Except ShuffleErr (Result source target spills) :=
      let top := state.stack.topOffset hne
      have htop : top.val = state.stack.length - 1 := rfl
      -- if the top is out of place, we swap it into position
      if ht : perm top ≠ top
      then
        let perm' := perm * Equiv.swap top (perm top)
        -- an equal slot standing at the desired offset serves the top's destination just as well
        if state.stack[perm top] = state.stack[top] then
          go { state with mapping := state.mapping.swapDestinations (perm top) top } perm' hne
        else if hreach : ¬ state.isSwapReachable (perm top) then
          state.blockSwapUnreachable (perm top)
        else if state.isFinal (perm top) then
          .error (.assertion "swapping a final slot out of place")
        else
          -- the top is out of place, so `perm top` is strictly below it
          have hvalid : state.stack.isValidSwapTarget (perm top) :=
            ⟨by have := (perm top).isLt; have := Fin.val_ne_of_ne ht; dsimp only; omega, not_not.mp hreach⟩
          go (state.swap (perm top) hvalid) (by simpa [Permutation] using perm') (by simpa using hne)

      -- search for the shallowest out of place element
      else
        -- we make pos a subtype that carries a proof that pos is out of place.
        -- we need this later to show that swapping it is valid
        let pos : Option {i : Fin state.stack.length // perm i ≠ i} :=
          (List.finRange state.stack.length).foldl
            (λ p (i : Fin state.stack.length) =>
              if h : perm i ≠ i then .some ⟨i, h⟩ else p)
            .none
        match pos with

        -- swap top with pos
        | some ⟨pos, hpos⟩ =>
          let perm' := perm * Equiv.swap top pos
          -- a misplaced slot equal to the top takes over the top's destination, making the top the misplaced
          -- one; it then travels to its destination directly instead of dislodging an in-place slot
          if state.stack[pos] = state.stack[top] then
            go { state with mapping := state.mapping.swapDestinations pos top } perm' hne
          else if hreach : ¬ state.isSwapReachable pos then
            state.blockSwapUnreachable pos
          else if state.isFinal pos then
            .error (.assertion "swapping a final slot out of place")
          else
            -- `top` is a fixed point, so the out-of-place `pos` is strictly below it
            have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
            have hvalid : state.stack.isValidSwapTarget pos :=
              ⟨by have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; dsimp only; omega, not_not.mp hreach⟩
            go (state.swap pos hvalid) (by simpa [Permutation] using perm') (by simpa using hne)

        -- we're done
        | none => .ok ⟨none, state⟩
    termination_by Permutation.measure perm (state.stack.topOffset hne)
    decreasing_by
      · exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm _ ht)
      · simp only [eq_mpr_eq_cast]
        rw [Permutation.measure_cast (State.swap_length _ _ hvalid).symm _ hne]
        exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm _ ht)
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm _ pos (not_not.mp ht) hpos
        exact Prod.Lex.right' _ heq.le hlt
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm _ pos (not_not.mp ht) hpos
        simp only [eq_mpr_eq_cast]
        rw [Permutation.measure_cast (State.swap_length _ _ hvalid).symm _ hne]
        exact Prod.Lex.right' _ heq.le hlt

-- applies the permutation perm to the source stack via the inverse equivalence
-- every proper permutation has an inverse
def apply_permutation (source : Stack) (perm : Permutation source) : Stack :=
  List.ofFn (λ k => source[perm.symm k])

def all_swaps_reachable (perm : Permutation source) : Prop
  := ∀ i ∈ perm.support, source.isSwapReachable i

-- Every position whose value must change is within SWAP reach.
def values_reachable {source : Stack} (perm : Permutation source) : Prop :=
  ∀ i : Fin source.length,
    source[i] ≠ source[perm.symm i] → source.isSwapReachable i

-- Every slot bound to a stack offset is bound to one that `perm` fills with an equal value.
def bindings_agree {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (perm : Permutation state.stack) : Prop :=
  ∀ (i : Fin state.stack.length) (d : Fin target.length) (h : d.val < state.stack.length),
    state.mapping i = some d → state.stack[perm.symm ⟨d.val, h⟩] = state.stack[i]

end Shuffler.Permute
