import Experiments.BuildBottomUp.Queries
import Shuffler.Permute.Defs

namespace BuildBottomUpExperiments.Checked

inductive Error where
  | blocked (excess : ℕ)
  | assertion (reason : String)
  deriving DecidableEq, Repr

abbrev Result (source : Stack) (spills : SpillSet) :=
  (res : Stack) × Trace spills source res

abbrev M := Except Error

-- PLift lets Except return the proof needed to construct dependent values.
def requires (condition : Prop) [Decidable condition] (reason : String) : M (PLift condition) :=
  if h : condition then pure ⟨h⟩ else throw (.assertion reason)

def ensure (condition : Prop) [Decidable condition] (reason : String) : M Unit := do
  let _ ← requires condition reason
  return ()

def liftResult (r : Except ShuffleErr α) : M α :=
  r.mapError fun (.Blocked excess) => .blocked excess

def index (size offset : ℕ) : M (Fin size) := do
  if h : offset < size then return ⟨offset, h⟩
  else throw (.assertion "offset is out of bounds")

def slotAt (stack : Stack) (offset : ℕ) : M Value := do
  return stack[← index stack.length offset]

def positionOf (state : State source target spills) (offset : ℕ) : Option ℕ :=
  if h : offset < target.length then (state.mapping.symm ⟨offset, h⟩).map Fin.val else none

def depthOf (state : State source target spills) (offset : ℕ) : ℕ :=
  state.stack.length - 1 - offset

def isSwapReachable (state : State source target spills) (offset : ℕ) : Prop :=
  depthOf state offset ≤ MAX_SWAP_DEPTH

instance (state : State source target spills) (offset : ℕ) :
    Decidable (isSwapReachable state offset) :=
  inferInstanceAs (Decidable (depthOf state offset ≤ MAX_SWAP_DEPTH))

instance (state : State source target spills) (dest : Fin target.length) :
    Decidable (state.isAvailable dest) := by
  unfold State.isAvailable
  infer_instance

-- Convert between source offsets and the depths used by trace constructors.
private theorem dup_stack_eq (stack : Stack) (copy : Fin stack.length) :
    stack ++ [stack[stack.length - ((stack.depth copy).val + 1)]] =
      stack ++ [stack[copy]] := by
  have hcopy : stack.length - ((stack.depth copy).val + 1) = copy.val := by
    dsimp [Stack.depth]; omega
  exact congrArg (fun slot => stack ++ [slot]) (getElem_congr_idx hcopy)

private theorem swap_stack_eq (stack : Stack) (pos : Fin stack.length) :
    stack.swap (stack.length - 1) (stack.length - 1 - (stack.depth pos).val) =
      stack.swap pos (stack.length - 1) := by
  have hpos : stack.length - 1 - (stack.depth pos).val = pos.val := by
    dsimp [Stack.depth]; omega
  rw [hpos, List.swap_comm]

private theorem swap_depth_pos (stack : Stack) (pos : Fin stack.length)
    (hbelow : pos.val + 1 < stack.length) : 1 ≤ (stack.depth pos).val := by
  dsimp [Stack.depth]; omega

private theorem top_lt_length (stack : Stack) (pos : Fin stack.length) :
    stack.length - 1 < stack.length := by
  have := pos.isLt
  omega

def push (state : State source target spills) (slot : Value) (dest : Fin target.length) : M (State source target spills) := do
  let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
  let ⟨hgen⟩ ← requires (slot.can_be_freely_generated ∨ spills.is_spilled slot) "pushed slot cannot be generated or loaded"
  have heq : state.stack.length + 1 = (state.stack ++ [slot]).length := by simp

  return {
    state with
    stack := state.stack ++ [slot]
    trace := match slot, hgen with
      | .Var id  , h => .Load id (by simpa [Value.can_be_freely_generated, SpillSet.is_spilled] using h) state.trace
      | .Lit word, _ => .Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace
      | .Wildcard, _ => .Push .Wildcard (by decide) state.trace
    mapping := heq ▸ state.mapping.push dest hbound
  }

def dup (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) : M (State source target spills) := do
  let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
  let ⟨hdup⟩ ← requires (state.stack.isDupReachable copy) "copy is outside DUP reach"
  let depth := state.stack.depth copy
  have heq : state.stack.length + 1 = (state.stack ++ [state.stack[copy]]).length := by simp

  return {
    state with
    stack := state.stack ++ [state.stack[copy]]
    trace :=
      dup_stack_eq state.stack copy ▸
        Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt) (Nat.succ_pos _) (Nat.add_le_add_right hdup 1) state.trace
    mapping := heq ▸ state.mapping.push dest hbound
  }

def swapDestinations (state : State source target spills) (a b : ℕ) : M (State source target spills) := do
  let a ← index state.stack.length a
  let b ← index state.stack.length b
  return { state with mapping := state.mapping.swapDestinations a b }

def swapWith (state : State source target spills) (offset : ℕ) : M (State source target spills) := do
  let pos ← index state.stack.length offset
  let ⟨hbelow, hreach, _hnfinal⟩ ← requires
    (pos.val + 1 < state.stack.length ∧ state.stack.isSwapReachable pos ∧ ¬ state.isFinal pos.val)
    "swap requires a reachable slot below the top that is not final"
  let depth := state.stack.depth pos
  have heq : state.stack.length = (state.stack.swap pos (state.stack.length - 1)).length :=
    List.length_swap.symm
  return {
    state with
    stack := state.stack.swap pos (state.stack.length - 1)
    mapping := heq ▸
      state.mapping.swapDestinations pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩
    trace := swap_stack_eq state.stack pos ▸ Trace.Swap depth.val depth.isLt
      (swap_depth_pos state.stack pos hbelow) hreach state.trace
  }

def produce (initial : State source target spills) (targetOffset : Fin target.length) : M (State source target spills) := do
  let mut state := initial
  ensure (state.mapping.symm targetOffset).isNone "destination already bound to a slot"

  let slot := target[targetOffset.val]
  let copy := state.stack.shallowestCopyPosition slot

  if slot.is_junk then
    state ← push state slot targetOffset
  else if let some pos := copy.filter (fun pos => state.stack.isDupReachable pos) then
    state ← dup state pos targetOffset
  else if slot.can_be_freely_generated ∨ spills.is_spilled slot then
    state ← push state slot targetOffset
  else if let some pos := copy then
    throw (.blocked (state.stack.depth pos - MAX_DUP_DEPTH))
  else
    throw (.assertion "generated slot has no copy on the stack and is not spilled")

  ensure (positionOf state targetOffset.val = some (state.stack.length - 1)) "generated slot is not bound to the top"
  state := { state with pending_generations := state.pending_generations - 1 }
  return state

def generate (initial : State source target spills) (targetOffset : ℕ) : M (State source target spills) := do
  let mut state := initial
  state ← produce state (← index target.length targetOffset)

  if targetOffset + 1 < state.stack.length ∧ ¬ state.isFinal targetOffset then
    let top := state.stack.length - 1
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack top) then
      state ← swapDestinations state targetOffset top
    else if isSwapReachable state targetOffset then
      state ← swapWith state targetOffset
  return state

end BuildBottomUpExperiments.Checked
