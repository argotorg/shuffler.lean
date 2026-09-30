import Shuffler.State

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

def Stack.depth (stack : Stack) (idx : Fin stack.length) : Fin stack.length :=
  ⟨stack.length - 1 - idx, by omega⟩

def Stack.isDupReachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.depth pos) ≤ MAX_DUP_DEPTH

def Stack.isSwapReachable (stack : Stack) (pos : Fin stack.length) : Prop :=
  (stack.depth pos) ≤ MAX_SWAP_DEPTH

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
