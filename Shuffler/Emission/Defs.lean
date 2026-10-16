import Mathlib.Data.Finset.Sort
import Shuffler.Contracts
import Shuffler.Mapping
import Shuffler.Stack
import Shuffler.Trace
import Std.Internal.Do
import Std.Tactic.Do

-- TODO: make numeric types here match the c++ types
-- TODO: make the Error.blocked args match the c++
-- TODO: add a Depth / Offset type
-- TODO: Dup should not accept a FunctionReturnLabel

-- The state and the shared helpers of the C++ `Emission` class. Its algorithms (removeSurplus,
-- buildBottomUp) live in their own folders and extend this namespace.

namespace Shuffler.Emission

-- `Error` and `requires` are shared with BuildMapping; re-export them for `open Shuffler.Emission`.
export Shuffler (Error requires)

variable {source target : Stack} {spills : SpillSet}

--- Types ------------------------------------------------------------------------------------------


-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:811-824.
structure State (source target : Stack) (spills : SpillSet) where
  -- The mapping as planned, before any operation
  planned_mapping : Mapping source.length target.length

  -- The working stack and its (in sync) mapping
  stack : Stack
  trace : Trace spills source stack
  mapping : Mapping stack.length target.length

  -- Number of target offsets whose slot still has to be produced; decremented by `produce`
  pending_generations : ℕ

--- Utils ------------------------------------------------------------------------------------------


-- convert offset to a `Fin size` if offset < size. throw an assertion error otherwise.
def index (size offset : ℕ) : Except Error (Fin size) := do
  if h : offset < size then return ⟨offset, h⟩
  else throw (.assertion "offset is out of bounds")

-- return the slot at offset if offset < stack.length. throw an assertion error otherwise.
def slotAt (stack : Stack) (offset : ℕ) : Except Error Value := do
  return stack[← index stack.length offset]


--- Conversions ------------------------------------------------------------------------------------


-- Depth of the slot at `offset` below the top of the working stack
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:741-744.
def State.depthOf (state : State source target spills) (offset : Fin state.stack.length) : Fin state.stack.length :=
  state.stack.offsetToDepth offset


--- Queries ----------------------------------------------------------------------------------------


-- The destination of the slot at `offset`: the target offset it is bound for, or none for a surplus slot.
-- Whether absence is expected is the caller's business - after `removeSurplus` every slot has one.
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:729-732.
def State.destinationOf (state : State source target spills) (offset : Fin state.stack.length) : Option (Fin target.length) :=
  state.mapping offset

-- The position of the slot bound for `offset`, or none if no slot is bound for it
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:84-87.
def State.positionOf (state : State source target spills) (offset : Fin target.length) : Option (Fin state.stack.length) :=
  state.mapping.symm offset

-- Whether a swap can reach the slot at `offset`; trivially true for the top itself
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:747-750.
def State.isSwapReachable (state : State source target spills) (offset : Fin state.stack.length) : Prop :=
  (state.depthOf offset).val ≤ MAX_SWAP_DEPTH

instance (state : State source target spills) (offset : Fin state.stack.length) :
    Decidable (state.isSwapReachable offset) := by unfold State.isSwapReachable; infer_instance

-- Whether the slot at `pos` is bound for `pos` itself, i.e., already is at its final target offset
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:735-738.
def State.isFinal (state : State source target spills) (pos : Fin state.stack.length) : Prop :=
  (state.destinationOf pos).map Fin.val = some pos.val

instance (state : State source target spills) (pos : Fin state.stack.length) :
    Decidable (state.isFinal pos) := by unfold State.isFinal; infer_instance

-- Whether the slot at `pos` has no target offset to go to and is to be popped
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:733-736 (at 6db6505).
def State.isSurplus (state : State source target spills) (pos : Fin state.stack.length) : Prop :=
  state.destinationOf pos = none

instance (state : State source target spills) (pos : Fin state.stack.length) :
    Decidable (state.isSurplus pos) := by unfold State.isSurplus; infer_instance

-- A swap cannot reach the slot at `pos`: it is out of reach by `depth - MAX_SWAP_DEPTH` slots
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:811-814 (at 6db6505).
def State.blockSwapUnreachable (state : State source target spills) (pos : Fin state.stack.length) : Error :=
  .blocked ((state.depthOf pos).val - MAX_SWAP_DEPTH)


--- Actions ----------------------------------------------------------------------------------------


-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:780-784.
def State.push (state : State source target spills)
    (slot : Value) (dest : Fin target.length) : Except Error (State source target spills) := do

  let ⟨hbound⟩ ← requires (state.positionOf dest = none) "destination already bound to a slot"
  let ⟨hgen⟩ ← requires (slot.can_be_freely_generated ∨ spills.is_spilled slot) "pushed slot cannot be generated or loaded"

  return {
    state with
    stack := state.stack ++ [slot]
    trace := match slot, hgen with
      | .Var id  , h => .Load id (by simpa [Value.can_be_freely_generated, SpillSet.is_spilled] using h) state.trace
      | .Lit word, _ => .Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace
      | .Wildcard, _ => .Push .Wildcard (by decide) state.trace
    mapping := by simpa [stack_push_len] using
      state.mapping.push dest hbound
  }

-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:786-790.
def State.dup (state : State source target spills)
    (offset : ℕ) (dest : Fin target.length) : Except Error (State source target spills) := do

  let copy ← index state.stack.length offset
  let depth := state.stack.offsetToDepth copy

  let ⟨hbound⟩ ← requires (state.positionOf dest = none) "destination already bound to a slot"
  let ⟨hdup⟩ ← requires (state.stack.isDupReachable copy) "Stack too deep"

  return {
    state with
    stack := state.stack ++ [state.stack[copy]]
    trace :=
      dup_stack_eq state.stack copy ▸
        Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt) (Nat.succ_pos _) (Nat.add_le_add_right hdup 1) state.trace
    mapping := by simpa [stack_push_len] using
      state.mapping.push dest hbound
  }

-- Exchanges the destinations of the slots at `a` and `b`
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:100-107.
def State.swapDestinations (state : State source target spills) (a b : ℕ)
    : Except Error (State source target spills) := do

  let a ← index state.stack.length a
  let b ← index state.stack.length b
  return { state with mapping := state.mapping.swapDestinations a b }

-- Swaps the top with the slot at `offset`, the destinations traveling along
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:767-772.
def State.swapWith (state : State source target spills)
    (offset : ℕ) : Except Error (State source target spills) := do

  let pos ← index state.stack.length offset
  let depth := state.stack.offsetToDepth pos

  _ ← requires (¬ state.isFinal pos) "swap target is already final"
  let ⟨hdepth⟩ ← requires (1 ≤ depth.val ∧ depth ≤ MAX_SWAP_DEPTH) "invalid swap target"

  return {
    state with
    stack := state.stack.swap pos (state.stack.length - 1)
    mapping := List.length_swap.symm ▸
      state.mapping.swapDestinations pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩
    trace := swap_stack_eq state.stack pos ▸
      Trace.Swap depth.val depth.isLt hdepth.1 hdepth.2 state.trace
  }

-- Removes the top slot together with its destination, if any
-- See solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp:785-789 (at 6db6505).
def State.pop (state : State source target spills) : Except Error (State source target spills) := do

  let ⟨hne⟩ ← requires (0 < state.stack.length) "pop on an empty stack"

  return {
    state with
    stack := state.stack.dropLast
    trace := .Pop hne state.trace
    mapping := Mapping.pop (cast (by rw [List.length_dropLast, Nat.sub_add_cancel hne]) state.mapping)
  }

end Shuffler.Emission
