module

public import Shuffler.Emission.Defs
public import Shuffler.Permute.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Factors

@[expose] public section

namespace Shuffler.Permute

open Emission

abbrev Permutation (n : ℕ) := Equiv.Perm (Fin n)

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
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:648-733.
def permute
  {source target : Stack} {spills : SpillSet}
  (initial : State source target spills)
  (perm : Permutation initial.stack.length)
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
    minimizePermutationSupport (stack : Stack) (perm : Permutation stack.length) (position : ℕ) : Permutation stack.length :=
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
    minimizeCyclesWithoutTop (stack : Stack) (perm : Permutation stack.length) : Permutation stack.length := Id.run do
      let mut perm := perm
      for a in List.finRange stack.length do
        if perm a ≠ a then
          for b in (List.finRange stack.length).drop (a.val + 1) do
            if stack[a] = stack[b] ∧ (perm b ≠ b ∨ b.val = stack.length - 1) then
              if ¬ perm.SameCycle a b then
                perm := perm * Equiv.swap a b
              break
      return perm

    -- Exchanges the slot at `pos` with the top, the destinations traveling along. The caller exchanges the
    -- corresponding destinations of the permutation.
    -- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:691-705.
    exchangeWithTop (state : State source target spills) (pos : ℕ) :
        Except ShuffleErr (Result source target spills) := do
      let top := state.stack.length - 1
      _ ← requires ((← slotAt state.stack pos) ≠ (← slotAt state.stack top)) "exchanging equal slots"
      let offset ← index state.stack.length pos
      if ¬ state.isSwapReachable offset then
        return ← state.blockSwapUnreachable offset
      return ⟨none, ← state.swapWith offset⟩

    go {n : ℕ} (state : State source target spills) (perm : Permutation n)
        (hne : n > 0) :
        Except ShuffleErr (Result source target spills) := do
      let top : Fin n := ⟨n - 1, by omega⟩
      -- if the top is out of place, we swap it into position
      if ht : perm top ≠ top
      then
        let perm' := perm * Equiv.swap top (perm top)
        let result ← exchangeWithTop state (perm top)
        if result.blocked.isSome then return result
        go result.state perm' hne

      -- search for the shallowest out of place element
      else
        -- we make pos a subtype that carries a proof that pos is out of place.
        -- we need this later to show that the measure decreases
        let pos : Option {i : Fin n // perm i ≠ i} :=
          (List.finRange n).foldl
            (λ p (i : Fin n) =>
              if h : perm i ≠ i then .some ⟨i, h⟩ else p)
            .none
        match pos with

        -- swap top with pos
        | some ⟨pos, hpos⟩ =>
          let perm' := perm * Equiv.swap top pos
          let result ← exchangeWithTop state pos
          if result.blocked.isSome then return result
          go result.state perm' hne

        -- we're done
        | none => .ok ⟨none, state⟩
    termination_by Permutation.measure perm ⟨n - 1, by omega⟩
    decreasing_by
      · exact Prod.Lex.left _ _ (Permutation.measure_place_top_lt perm _ ht)
      · obtain ⟨heq, hlt⟩ := Permutation.measure_swap_pos_lt perm _ pos (not_not.mp ht) hpos
        exact Prod.Lex.right' _ heq.le hlt

-- applies the permutation perm to the source stack via the inverse equivalence
-- every proper permutation has an inverse
def apply_permutation (source : Stack) (perm : Permutation source.length) : Stack :=
  List.ofFn (λ k => source[perm.symm k])

def all_swaps_reachable {source : Stack} (perm : Permutation source.length) : Prop
  := ∀ i ∈ perm.support, source.isSwapReachable i

-- Every position whose value must change is within SWAP reach.
def values_reachable {source : Stack} (perm : Permutation source.length) : Prop :=
  ∀ i : Fin source.length,
    source[i] ≠ source[perm.symm i] → source.isSwapReachable i

-- Every slot bound to a stack offset is bound to one that `perm` fills with an equal value.
def bindings_agree {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (perm : Permutation state.stack.length) : Prop :=
  ∀ (i : Fin state.stack.length) (d : Fin target.length) (h : d.val < state.stack.length),
    state.mapping i = some d → state.stack[perm.symm ⟨d.val, h⟩] = state.stack[i]

end Shuffler.Permute
