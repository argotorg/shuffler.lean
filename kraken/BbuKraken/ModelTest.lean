import BbuKraken.Fn.Loop.Defs

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

/-! ## `finish`: `permuteDestinations` -/

#guard ok? (finish ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩)
  = some ⟨[⟨x, 0⟩, ⟨y, 1⟩], [some 0, some 1], 0, []⟩
#guard ok? (finish ⟨[], [], 0, []⟩) = some ⟨[], [], 0, []⟩
-- Two slots for one offset: not a permutation.
#guard assertion? (finish ⟨[⟨x, 0⟩, ⟨y, 0⟩], [some 1, none], 0, []⟩)
-- Each slot has a destination, so the `has_value` check always holds.
example (st : St) : (List.range st.len).all (fun pos => (st.destinationOf pos).isSome) = true :=
  St.all_destinationOf st

end Bbu.ModelTest
