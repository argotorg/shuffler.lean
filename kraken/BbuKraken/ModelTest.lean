module

public import BbuKraken.Fn.Loop.Defs
import all BbuKraken.Fn.Loop.Defs

@[expose] public section

/-!
Tests of the checks of `Model.lean` that follow `c/build_bottom_up.cpp`: the
count of the constructor, the size_t wrap of `pendingGenerations`, the reads and
asserts of the bound branch, the checks of `swapDestinations` and
`permuteDestinations`, and the order of `add`.
-/

namespace Bbu.ModelTest

open Bbu

def x : StackSlot := ⟨1, Value, Const⟩
def y : StackSlot := ⟨2, Value, Const⟩

def env (n : Nat) : Env := ⟨List.replicate n x, fun _ => 0⟩

def ok? {α : Type} : M α → Option α
  | .ok a => some a
  | .error _ => none

def assertion? {α : Type} : M α → Bool
  | .error .assertion => true
  | _ => false

def blocked? {α : Type} : M α → Option (Nat × Nat × St)
  | .error (.blocked pos excess st) => some (pos, excess, st)
  | _ => none

/-! ## `init`: the constructor counts the offsets with no slot -/

-- Two slots bound for `2` and `0`: only offset `1` is unbound.
#guard (init (env 3) [x, y] [2, 0]).pendingGenerations = 1
#guard (init (env 3) [] []).pendingGenerations = 3
#guard (init (env 0) [] []).pendingGenerations = 0
-- A destination out of range binds no offset: the count is `3`, not `n - m = 2`.
#guard (init (env 3) [x] [5]).pendingGenerations = 3
-- Two slots for one offset: the count is `2`, not `n - m = 1`.
#guard (init (env 3) [x, y] [0, 0]).pendingGenerations = 2

/-! ## `produce`: `--m_pendingGenerations` on a size_t -/

#guard sizeDec 0 = 2 ^ 64 - 1
#guard sizeDec 1 = 0
#guard sizeDec 5 = 4

def st0 (p : Nat) : St := ⟨[], [none], p, []⟩

#guard (ok? (produce (env 1) (st0 1) 0)).map St.pendingGenerations = some 0
-- `pendingGenerations = 0` wraps.
#guard (ok? (produce (env 1) (st0 0) 0)).map St.pendingGenerations = some (2 ^ 64 - 1)

/-! ## `add`: the stack operation, then the assert, then the bind -/

#guard ok? (add (st0 1) x 0 (.push x)) = some ⟨[⟨x, 0⟩], [some 0], 1, [.push x]⟩
-- The destination is bound already: the assert fires.
#guard assertion? (add ⟨[⟨y, 0⟩], [some 0], 1, []⟩ x 0 (.push x))

/-! ## `swapDestinations`: `if (destination) m_positionOf[*destination] = pos` -/

#guard bindIf [none, none] none 1 = [none, none]
#guard bindIf [none, none] (some 1) 0 = [none, some 0]

-- Slots `0` and `1` swap their destinations; both offsets follow.
#guard swapDestinations ⟨[⟨x, 1⟩, ⟨y, 0⟩], [some 1, some 0], 0, []⟩ 0 1
  = ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩
-- Position `5` is above the top: it has no destination, so `m_positionOf` gets no
-- write for it.
#guard (swapDestinations ⟨[⟨x, 1⟩], [none, some 0], 0, []⟩ 0 5).positionOf = [some 0, some 0]

/-! ## `takeBound`: the bound branch -/

-- Offset `0` has no slot: the `has_value` assert fires.
#guard assertion? (takeBound ⟨[⟨x, 1⟩], [none, some 0], 1, []⟩ 0)
-- The slot for offset `1` is at `0 < 1`: the `>=` assert fires.
#guard assertion? (takeBound ⟨[⟨x, 1⟩, ⟨y, 0⟩], [some 1, some 0], 0, []⟩ 1)
-- The slot at `0` has the value of the slot bound for `0`: `pos = targetOffset`.
#guard ok? (takeBound ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, []⟩ 0)
  = some (⟨[⟨x, 0⟩, ⟨x, 1⟩], [some 0, some 1], 0, []⟩, true)
-- The values differ: the copy at `2` goes to `0`, and the value check passes.
#guard ok? (takeBound ⟨[⟨y, 1⟩, ⟨x, 0⟩, ⟨x, 3⟩], [some 1, some 0, none, some 2], 1, []⟩ 0)
  = some (⟨[⟨y, 1⟩, ⟨x, 3⟩, ⟨x, 0⟩], [some 2, some 0, none, some 1], 1, []⟩, false)
-- The value check of `takeBound` (`afterPos` in the proof of the loop) fires for a
-- slot with another value.
#guard assertion? (Loop.afterPos ⟨[⟨y, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, []⟩ 0 1 0)
#guard (ok? (Loop.afterPos ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, []⟩ 0 1 0)).isSome

-- `step` takes the bound branch when `positionOf` has a value.
#guard ok? (step (env 2) ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 1, []⟩ 0)
  = some (⟨[⟨x, 0⟩, ⟨x, 1⟩], [some 0, some 1], 1, []⟩, .next 1)

/-! ## `finishC`: `permuteDestinations` of the C++ -/

#guard ok? (finishC ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩)
  = some ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩
#guard ok? (finishC ⟨[], [], 0, []⟩) = some ⟨[], [], 0, []⟩
-- Two slots for one offset: not a permutation.
#guard assertion? (finishC ⟨[⟨x, 0⟩, ⟨y, 0⟩], [some 1, none], 0, []⟩)
-- Equal slots: `permute` does not group them, so it swaps them. The swaps
-- move the values; the destinations stay at their positions.
#guard ok? (finishC ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, []⟩)
  = some ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, [.swap 1]⟩

/-! ## `finish`: `Permute.permute` of the original -/

-- `List.dedup` keeps the last copy of each element.
#guard dedup [x, y, x] = [y, x]
#guard dedup ([] : List StackSlot) = []
#guard dedup [1, 1, 1] = [1]
#guard dedup [3, 1, 2] = [3, 1, 2]

-- `Equiv.setValue`: `0` goes to `0`, and `2`, which went to `0`, goes where `0` went.
#guard setValue [1, 2, 0] 0 0 = [0, 2, 1]
-- `a` goes to `b` already: no change.
#guard setValue [1, 2, 0] 1 2 = [1, 2, 0]

-- The group of `x` at `0` and `2` goes to `{0, 1}`: `0` stays, `2` takes `1`.
#guard ok? (normalize [x, y, x] [1, 2, 0]) = some [0, 2, 1]
-- One slot of each value: no change.
#guard ok? (normalize [x, y] [1, 0]) = some [1, 0]
#guard ok? (normalize [] []) = some []
-- Not a permutation: the group has more movers than vacant offsets.
#guard assertion? (normalize [x, x] [0, 0])

#guard ok? (finish ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩)
  = some ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩
#guard ok? (finish ⟨[], [], 0, []⟩) = some ⟨[], [], 0, []⟩
-- Two slots for one offset: not a permutation.
#guard assertion? (finish ⟨[⟨x, 0⟩, ⟨y, 0⟩], [some 1, none], 0, []⟩)
-- Two values: one swap, and the destinations travel with the slots.
#guard ok? (finish ⟨[⟨x, 1⟩, ⟨y, 0⟩], [some 1, some 0], 0, []⟩)
  = some ⟨[⟨y, 0⟩, ⟨x, 1⟩], [some 0, some 1], 0, [.swap 1]⟩
-- Equal slots: the normalized permutation is the identity, so there is no
-- swap, and the mapping does not change.
#guard ok? (finish ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, []⟩)
  = some ⟨[⟨x, 1⟩, ⟨x, 0⟩], [some 1, some 0], 0, []⟩
-- The group of `x` goes to `{0, 1}`: one swap brings `y` to the top.
#guard ok? (finish ⟨[⟨x, 1⟩, ⟨y, 2⟩, ⟨x, 0⟩], [some 2, some 0, some 1], 0, []⟩)
  = some ⟨[⟨x, 1⟩, ⟨x, 0⟩, ⟨y, 2⟩], [some 1, some 0, some 2], 0, [.swap 1]⟩
-- After two swaps the slot at `1` equals the top: it takes the destination of
-- the top with no swap (the retag of `permute.go`).
#guard ok? (finish ⟨[⟨x, 2⟩, ⟨y, 0⟩, ⟨x, 1⟩], [some 1, some 2, some 0], 0, []⟩)
  = some ⟨[⟨y, 0⟩, ⟨x, 2⟩, ⟨x, 1⟩], [some 0, some 2, some 1], 0, [.swap 1, .swap 2]⟩

-- 18 slots of distinct values.
def wide (dests : List Nat) : St :=
  let slots := (List.range 18).zipWith (fun i d => (⟨⟨.ofNat 32 i, Value, 1⟩, d⟩ : Slot)) dests
  ⟨slots, (List.range 18).map fun d => dests.idxOf? d, 0, []⟩

-- The top goes to `0` at depth 17: blocked by 1, with the state before any swap.
def wide0 : St := wide (17 :: (List.range 16).map (· + 1) ++ [0])
#guard blocked? (finish wide0) = some (0, 1, wide0)
-- One swap at depth 1, then the top goes to `0`: the block keeps the swap.
def wide1 : St := wide (17 :: (List.range 15).map (· + 1) ++ [0, 16])
#guard match blocked? (finish wide1) with
  | some (0, 1, st) => st.trace = [.swap 1] && st.len = 18
  | _ => false
-- The block of `finishC` keeps the state before the swaps.
#guard blocked? (finishC wide1) = some (0, 1, wide1)

-- `buildBottomUp` and `buildBottomUpC` differ on equal slots.
#guard (ok? (buildBottomUp ⟨[x, x], fun _ => 0⟩ [x, x] [1, 0])).map St.trace = some []
#guard (ok? (buildBottomUpC ⟨[x, x], fun _ => 0⟩ [x, x] [1, 0])).map St.trace = some [.swap 1]

/-! ## `emit`: a function return label is not copied -/

def r : StackSlot := ⟨7, FunctionReturnLabel, 1⟩
def v : StackSlot := ⟨7, Value, 1⟩

-- A copy in reach: the dup of a label fails, the dup of a variable passes.
#guard assertion? (emit ⟨[r, r], fun _ => 0⟩ ⟨[⟨r, 1⟩], [none, some 0], 1, []⟩ 0)
#guard ok? (emit ⟨[v, v], fun _ => 0⟩ ⟨[⟨v, 1⟩], [none, some 0], 1, []⟩ 0)
  = some ⟨[⟨v, 1⟩, ⟨v, 0⟩], [some 1, some 0], 1, [.dup 1]⟩
-- No copy: a label that is not a literal is not pushed.
#guard assertion? (emit ⟨[r], fun _ => 0⟩ ⟨[], [none], 1, []⟩ 0)

end Bbu.ModelTest
