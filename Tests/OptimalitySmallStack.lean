import Shuffler.BuildBottomUp.Optimality.Theorems
import Tests.BuildBottomUpObservations

open Shuffler.Optimality.BBU Shuffler.BuildBottomUp BuildBottomUpTestSupport

namespace OptimalitySmallStackTests

private def swaps (result : Except Error ((res : Stack) × Trace spills source res)) :
    Except Error Nat :=
  result.map (·.2.swapCount)

-- The Bool form of State.Valid.
private def valid (state : State source target spills) : Bool :=
  decide (state.stack.length + state.pending_generations = target.length) &&
  decide (state.mapping.unmapped_target_slots = state.pending_generations) &&
  decide (∀ i, state.isAvailable i)

/-! The bound. -/

#guard smallSwapBound 0 1 = 0
#guard smallSwapBound 0 40 = 0
#guard smallSwapBound 1 0 = 0
#guard smallSwapBound 1 1 = 1
#guard smallSwapBound 1 2 = 1
#guard smallSwapBound 1 16 = 1
#guard smallSwapBound 1 17 = 2
#guard smallSwapBound 1 32 = 2
#guard smallSwapBound 1 33 = 3

/-! The n = 1 family: one SWAP for each block of 16 pending generations. -/

#guard valid (oneState 1)
#guard valid (oneState 17)
#guard swaps (buildBottomUp (oneState 1) (one_valid _)) = .ok 1
#guard swaps (buildBottomUp (oneState 2) (one_valid _)) = .ok 1
#guard swaps (buildBottomUp (oneState 15) (one_valid _)) = .ok 1
#guard swaps (buildBottomUp (oneState 16) (one_valid _)) = .ok 1
#guard swaps (buildBottomUp (oneState 17) (one_valid _)) = .ok 2
#guard swaps (buildBottomUp (oneState 32) (one_valid _)) = .ok 2
#guard swaps (buildBottomUp (oneState 33) (one_valid _)) = .ok 3
#guard (List.range 80).all fun k =>
  decide (swaps (buildBottomUp (oneState (k + 1)) (one_valid _)) = .ok (smallSwapBound 1 (k + 1)))

-- Negative cases: the count is not 1 past k = 16, and not 2 at k = 16.
#guard swaps (buildBottomUp (oneState 17) (one_valid _)) ≠ .ok 1
#guard swaps (buildBottomUp (oneState 16) (one_valid _)) ≠ .ok 2

/-! The n = 0 family emits no SWAP. -/

#guard valid (zeroState 0)
#guard (List.range 80).all fun k => decide (swaps (buildBottomUp (zeroState k) (zero_valid k)) = .ok 0)

/-! The theorems at the k = 0, k = 1 and k = 2 edges. -/

example : smallSwapBound 1 1 = 1 ∧ smallSwapBound 1 2 = 1 ∧ smallSwapBound 0 1 = 0 :=
  ⟨rfl, rfl, rfl⟩

example (n : Nat) (hn : n ≤ 1) := smallSwap_isGreatest n 0 hn
example := smallSwap_isGreatest 1 1 le_rfl
example := smallSwap_isGreatest 1 2 le_rfl
example := smallSwap_isGreatest 0 2 (by omega)

/-! Negative cases for n = 2: these Valid states exceed smallSwapBound 2 k, so the
theorems need n ≤ 1. -/

-- Bind source slot i to target dests[i]. A clash leaves the slot unbound.
private def ofDests (n size : Nat) (dests : List Nat) : Mapping n size :=
  (List.finRange n).foldl (init := ⊥) fun mapping p =>
    if hd : dests[p.val]?.getD size < size then
      if hp : mapping p = none then
        if hs : mapping.symm ⟨_, hd⟩ = none then mapping.bind p ⟨_, hd⟩ hp hs else mapping
      else mapping
    else mapping

private def pairState (source target : Stack) (dests : List Nat) : State source target ∅ :=
  let mapping := ofDests source.length target.length dests
  { planned_mapping := mapping
    stack := source
    trace := .Lit source
    mapping
    pending_generations := target.length - source.length }

-- k = 1: the two source values trade places and target 2 is a fresh literal.
private def pair1 := pairState [.Lit 0, .Lit 1] [.Lit 1, .Lit 0, .Lit 2] [1, 0]

#guard valid pair1
#guard pair1.positionOfNat 0 = some 1 ∧ pair1.positionOfNat 1 = some 0 ∧ pair1.positionOfNat 2 = none
#guard pair1.pending_generations = 1
#guard swaps (runIfValid pair1) = .ok 3
#guard smallSwapBound 2 1 < 3

-- k = 2: slot 0 holds an unspilled variable bound to target 3, and target 2 is its copy.
private def pair2 :=
  pairState [.Var ⟨0⟩, .Lit 1] [.Lit 1, .Lit 2, .Var ⟨0⟩, .Var ⟨0⟩] [3, 0]

#guard valid pair2
#guard pair2.positionOfNat 0 = some 1 ∧ pair2.positionOfNat 3 = some 0
#guard pair2.pending_generations = 2
#guard swaps (runIfValid pair2) = .ok 4
#guard smallSwapBound 2 2 < 4

-- An invalid state is outside the theorems: this one has a pending count that disagrees with
-- the unbound target count.
private def invalid : State [.Lit 0] [.Lit 0, .Lit 1] ∅ :=
  { pairState [.Lit 0] [.Lit 0, .Lit 1] [0] with pending_generations := 2 }

#guard !valid invalid

end OptimalitySmallStackTests
