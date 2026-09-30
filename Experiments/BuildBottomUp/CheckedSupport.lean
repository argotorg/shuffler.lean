import Shuffler.BuildBottomUp.Defs
import Std.Tactic.Do

namespace BuildBottomUpExperiments.Checked
open Shuffler.Permute

inductive Assertion where
  | bounds | bound | unavailable | swap | permutation | copy | final | size
  deriving DecidableEq, Repr

inductive Error where
  | blocked (excess : ℕ)
  | assertion (reason : Assertion)
  deriving DecidableEq, Repr

abbrev Result (source : Stack) (spills : SpillSet) :=
  (res : Stack) × Trace spills source res

abbrev M := Except Error

def liftResult (r : Except ShuffleErr α) : M α :=
  r.mapError fun (.Blocked excess) => .blocked excess

def assertThat (condition : Prop) [Decidable condition] (reason : Assertion) : M Unit :=
  if condition then pure () else throw (.assertion reason)

def index (size offset : ℕ) : M (Fin size) :=
  if h : offset < size then .ok ⟨offset, h⟩ else .error (.assertion .bounds)

def slotAt (stack : Stack) (offset : ℕ) : M Value := do
  return stack[← index stack.length offset]

def positionOf (state : State source target spills) (offset : ℕ) : Option ℕ :=
  if h : offset < target.length then (state.mapping.symm ⟨offset, h⟩).map Fin.val else none

def depthOf (state : State source target spills) (offset : ℕ) : ℕ :=
  state.stack.length - 1 - offset

def isSwapReachable (state : State source target spills) (offset : ℕ) : Bool :=
  depthOf state offset ≤ MAX_SWAP_DEPTH

instance (state : State source target spills) (dest : Fin target.length) :
    Decidable (state.is_available dest) := by
  unfold State.is_available
  infer_instance

def generate (state : State source target spills) (offset : ℕ) : M (State source target spills) := do
  let dest ← index target.length offset
  if hbound : state.mapping.symm dest = none then
    if havailable : state.is_available dest then
      return ← liftResult (state.generate dest hbound havailable)
    else
      throw (.assertion .unavailable)
  else
    throw (.assertion .bound)

def swapDestinations (state : State source target spills) (a b : ℕ) : M (State source target spills) := do
  let a ← index state.stack.length a
  let b ← index state.stack.length b
  return { state with mapping := state.mapping.swapDestinations a b }

def swapWith (state : State source target spills) (offset : ℕ) : M (State source target spills) := do
  let pos ← index state.stack.length offset
  if hbelow : pos.val + 1 < state.stack.length then
    if hreach : state.stack.is_swap_reachable pos then
      if hnfinal : ¬ state.is_final pos.val then
        return state.swapWith pos hbelow hreach hnfinal
  throw (.assertion .swap)

def finish (state : State source target spills) : M (Result source spills) := do
  if hlen : state.stack.length = target.length then
    if hsource : ∀ i, (state.mapping i).isSome then
      let ⟨res, trace⟩ ← liftResult (permute spills state.stack (state.mapping.toPermutation hlen hsource))
      return ⟨res, state.trace.concat trace⟩
  throw (.assertion .permutation)

end BuildBottomUpExperiments.Checked
