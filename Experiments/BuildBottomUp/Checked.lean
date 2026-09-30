import Shuffler.State
import Shuffler.Permute.Defs

-- An offset is final when its assigned source has the same offset.
-- Offsets outside the target's bounds are not final.
def State.isFinal (state : State source target spills) (offset : ℕ) : Prop :=
  if h : offset < target.length then
    (state.mapping.symm ⟨offset, h⟩).map Fin.val = some offset
  else False

instance (state : State source target spills) (offset : ℕ) :
    Decidable (state.isFinal offset) := by
  unfold State.isFinal
  infer_instance

def Stack.shallowestCopyPosition (stack : Stack) (slot : Value) :
    Option (Fin stack.length) :=
  (List.finRange stack.length).reverse.find?
    (fun pos => stack[pos] = slot)

def Stack.offsetToDepth (stack : Stack) (idx : Fin stack.length) : Fin stack.length :=
  ⟨stack.length - 1 - idx, by omega⟩

def Stack.isDupReachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.offsetToDepth pos) ≤ MAX_DUP_DEPTH

def Stack.isSwapReachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.offsetToDepth pos) ≤ MAX_SWAP_DEPTH

def State.isAvailable (state : State source target spills) (target_offset : Fin target.length) : Prop :=
  let slot := target[target_offset]
  slot.can_be_freely_generated ∨ spills.is_spilled slot ∨ (state.stack.shallowestCopyPosition slot).isSome

instance (stack : Stack) (pos : Fin stack.length) :
    Decidable (stack.isDupReachable pos) := by
  unfold Stack.isDupReachable
  infer_instance

instance (stack : Stack) (pos : Fin stack.length) :
    Decidable (stack.isSwapReachable pos) := by
  unfold Stack.isSwapReachable
  infer_instance

namespace BuildBottomUpExperiments.Checked

inductive Error where
  | blocked (excess : ℕ)
  | assertion (reason : String)
  deriving DecidableEq, Repr

abbrev Result (source : Stack) (spills : SpillSet) :=
  (res : Stack) × Trace spills source res

abbrev M := Except Error

abbrev Action (source target : Stack) (spills : SpillSet) :=
  StateT (State source target spills) M

-- Execute an update and retain its state. Errors have no state, as in M.
def Action.exec (action : Action source target spills Unit) (state : State source target spills) :
    M (State source target spills) := do
  let (_, next) ← action.run state
  return next

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
    stack ++ [stack[stack.length - ((stack.offsetToDepth copy).val + 1)]] =
      stack ++ [stack[copy]] := by
  have hcopy : stack.length - ((stack.offsetToDepth copy).val + 1) = copy.val := by
    dsimp [Stack.offsetToDepth]; omega
  exact congrArg (fun slot => stack ++ [slot]) (getElem_congr_idx hcopy)

private theorem swap_stack_eq (stack : Stack) (pos : Fin stack.length) :
    stack.swap (stack.length - 1) (stack.length - 1 - (stack.offsetToDepth pos).val) =
      stack.swap pos (stack.length - 1) := by
  have hpos : stack.length - 1 - (stack.offsetToDepth pos).val = pos.val := by
    dsimp [Stack.offsetToDepth]; omega
  rw [hpos, List.swap_comm]

private theorem swap_depth_pos (stack : Stack) (pos : Fin stack.length)
    (hbelow : pos.val + 1 < stack.length) : 1 ≤ (stack.offsetToDepth pos).val := by
  dsimp [Stack.offsetToDepth]; omega

private theorem top_lt_length (stack : Stack) (pos : Fin stack.length) :
    stack.length - 1 < stack.length := by
  have := pos.isLt
  omega

def push (slot : Value) (dest : Fin target.length) : Action source target spills Unit := do
  let state ← get
  let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
  let ⟨hgen⟩ ← requires (slot.can_be_freely_generated ∨ spills.is_spilled slot) "pushed slot cannot be generated or loaded"
  have heq : state.stack.length + 1 = (state.stack ++ [slot]).length := by simp

  set {
    state with
    stack := state.stack ++ [slot]
    trace := match slot, hgen with
      | .Var id  , h => .Load id (by simpa [Value.can_be_freely_generated, SpillSet.is_spilled] using h) state.trace
      | .Lit word, _ => .Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace
      | .Wildcard, _ => .Push .Wildcard (by decide) state.trace
    mapping := heq ▸ state.mapping.push dest hbound
  }

def dup (offset : ℕ) (dest : Fin target.length) : Action source target spills Unit := do
  let state ← get
  let copy ← index state.stack.length offset
  let depth := state.stack.offsetToDepth copy

  have heq : state.stack.length + 1 = (state.stack ++ [state.stack[copy]]).length := by simp
  let ⟨hbound⟩ ← requires (state.mapping.symm dest = none) "destination already bound to a slot"
  let ⟨hdup⟩ ← requires (state.stack.isDupReachable copy) "copy is outside DUP reach"

  set {
    state with
    stack := state.stack ++ [state.stack[copy]]
    trace :=
      dup_stack_eq state.stack copy ▸
        Trace.Dup (depth.val + 1) (Nat.succ_le_of_lt depth.isLt) (Nat.succ_pos _) (Nat.add_le_add_right hdup 1) state.trace
    mapping := heq ▸ state.mapping.push dest hbound
  }

def swapDestinations (a b : ℕ) : Action source target spills Unit := do
  let state ← get
  let a ← index state.stack.length a
  let b ← index state.stack.length b
  set { state with mapping := state.mapping.swapDestinations a b }

def swapWith (offset : ℕ) : Action source target spills Unit := do
  let state ← get
  let pos ← index state.stack.length offset
  let ⟨hbelow, hreach, _hnfinal⟩ ← requires
    (pos.val + 1 < state.stack.length ∧ state.stack.isSwapReachable pos ∧ ¬ state.isFinal pos.val)
    "swap requires a reachable slot below the top that is not final"
  let depth := state.stack.offsetToDepth pos
  have heq : state.stack.length = (state.stack.swap pos (state.stack.length - 1)).length :=
    List.length_swap.symm
  set {
    state with
    stack := state.stack.swap pos (state.stack.length - 1)
    mapping := heq ▸
      state.mapping.swapDestinations pos ⟨state.stack.length - 1, top_lt_length state.stack pos⟩
    trace := swap_stack_eq state.stack pos ▸ Trace.Swap depth.val depth.isLt
      (swap_depth_pos state.stack pos hbelow) hreach state.trace
  }

def produce (targetOffset : Fin target.length) : Action source target spills Unit := do
  let state ← get
  ensure (state.mapping.symm targetOffset).isNone "destination already bound to a slot"

  let slot := target[targetOffset.val]
  let copy := state.stack.shallowestCopyPosition slot

  if slot.is_junk then
    push slot targetOffset
  else if let some pos := copy.filter (fun pos => state.stack.isDupReachable pos) then
    dup pos.val targetOffset
  else if slot.can_be_freely_generated ∨ spills.is_spilled slot then
    push slot targetOffset
  else if let some pos := copy then
    throw (.blocked (state.stack.offsetToDepth pos - MAX_DUP_DEPTH))
  else
    throw (.assertion "generated slot has no copy on the stack and is not spilled")

  let state ← get
  ensure (positionOf state targetOffset.val = some (state.stack.length - 1)) "generated slot is not bound to the top"
  modify fun state => { state with pending_generations := state.pending_generations - 1 }

def generate (targetOffset : ℕ) : Action source target spills Unit := do
  produce (← index target.length targetOffset)
  let state ← get

  if targetOffset + 1 < state.stack.length ∧ ¬ state.isFinal targetOffset then
    let top := state.stack.length - 1
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack top) then
      swapDestinations targetOffset top
    else if isSwapReachable state targetOffset then
      swapWith targetOffset

-- StateT passes the working state between actions.
-- C++ ++targetOffset is written at each advancing continue and at the loop tail.
-- C++ --targetOffset; continue is a plain continue here.
def buildBottomUp (cursor : ℕ) (initial : State source target spills) : M (Result source spills) :=
  StateT.run' (s := initial) do
    let mut targetOffset := cursor
    while targetOffset < target.length do
      let state ← get
      if targetOffset < state.stack.length ∧ state.isFinal targetOffset then
        targetOffset := targetOffset + 1
        continue

      if state.pending_generations = 0 then
        let ⟨hlen, hsource⟩ ← requires
          (state.stack.length = target.length ∧ ∀ i, (state.mapping i).isSome)
          "stack does not define a complete permutation"
        let ⟨res, trace⟩ ← liftResult
          (Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hsource))
        return ⟨res, state.trace.concat trace⟩

      let urgentToDup ← forIn (m := M) [targetOffset : target.length] none fun offset urgent => do
        if (positionOf state offset).isSome then
          return .yield urgent
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          return .yield urgent
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked (depthOf state copy - MAX_DUP_DEPTH))
          if depthOf state copy = MAX_DUP_DEPTH ∧ copy.val ≠ targetOffset ∧ urgent.isNone then
            return .yield (some offset)
        return .yield urgent

      if h : urgentToDup.isSome ∧ urgentToDup ≠ some targetOffset ∧
          state.stack.length - targetOffset < MAX_SWAP_DEPTH then
        generate (urgentToDup.get h.1)
        continue

      let sourceTop := state.stack.length
      if urgentToDup.isNone ∧ sourceTop > targetOffset ∧ sourceTop < target.length ∧
          (positionOf state sourceTop).isNone ∧ sourceTop - targetOffset < MAX_SWAP_DEPTH then
        generate sourceTop
        continue

      if let some boundForTarget := positionOf state targetOffset then
        -- The slot bound for this offset must not be below it.
        ensure (boundForTarget ≥ targetOffset)
          "slot bound for the offset being filled is missing or already below it"
        let sourceForTargetOffset := boundForTarget
        let mut pos := sourceForTargetOffset
        if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
          pos := targetOffset
        else
          pos ← forIn (m := M)
            ((List.range state.stack.length).reverse.take (depthOf state sourceForTargetOffset)) pos fun candidate pos => do
              if (← slotAt state.stack candidate) = (← slotAt state.stack sourceForTargetOffset) ∧
                  ¬ state.isFinal candidate then
                return .done candidate
              return .yield pos

        ensure ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset))
          "selected copy differs from the bound slot"
        swapDestinations pos sourceForTargetOffset
        if pos = targetOffset then
          targetOffset := targetOffset + 1
          continue

        let state ← get
        if pos ≠ state.stack.length - 1 then
          if ¬ isSwapReachable state pos then
            throw (.blocked (depthOf state pos - MAX_SWAP_DEPTH))
          swapWith pos
      else
        generate targetOffset
        let state ← get
        if state.isFinal targetOffset then
          targetOffset := targetOffset + 1
          continue

      let state ← get
      ensure (¬ state.isFinal targetOffset) "target slot is already final"
      if targetOffset ≠ state.stack.length - 1 then
        if ¬ isSwapReachable state targetOffset then
          throw (.blocked (depthOf state targetOffset - MAX_SWAP_DEPTH))
        swapWith targetOffset
      targetOffset := targetOffset + 1

    let state ← get
    ensure (state.stack.length = target.length) "stack and target sizes differ"
    return ⟨state.stack, state.trace⟩

end BuildBottomUpExperiments.Checked
