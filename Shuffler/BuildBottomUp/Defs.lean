import Shuffler.Mapping
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

open Shuffler.Permute

def unmapped_target_slots (mapping : Mapping source target) : ℕ :=
  (Finset.univ.filter (λ j => mapping.symm j = .none)).card

theorem unmapped_target_slots_eq_zero (mapping : Mapping source target) :
    unmapped_target_slots mapping = 0 ↔ ∀ j, (mapping.symm j).isSome := by
  simp [unmapped_target_slots, Finset.filter_eq_empty_iff, Option.isSome_iff_ne_none]

-- TODO: can we refine the domain here?
abbrev SpillSet := Finset ℕ

def SpillSet.is_spilled (spills : SpillSet) : (val : Value) → Prop
| .Var idx => idx ∈ spills
| _ => false

instance (spills : SpillSet) (v : Value) : Decidable (spills.is_spilled v) := by
  cases v <;> unfold SpillSet.is_spilled <;> infer_instance

structure State (source target : Stack) where
  planned_mapping : Mapping source target

  stack : Stack
  trace : Trace source stack
  mapping : Mapping stack target

  pending_generations : ℕ
  hpending : unmapped_target_slots mapping = pending_generations

  spills : SpillSet




def State.is_final (state : State source target) (target_offset : Fin target.length)
  := (state.mapping.symm target_offset).map Fin.val = some target_offset.val

instance (state : State source target) (target_offset : Fin target.length) :
    Decidable (state.is_final target_offset) := by
  unfold State.is_final
  infer_instance

def LoopInvariant
    (target_offset : Fin target.length)
    (state : State source target) : Prop :=
  ∀ i : Fin target.length, i < target_offset → state.is_final i

theorem LoopInvariant.advance
    {target_offset : Fin target.length}
    {state : State source target}
    [NeZero target.length]
    (hinv : LoopInvariant target_offset state)
    (hfinal : state.is_final target_offset)
    (hnext : target_offset.val + 1 < target.length) :
    LoopInvariant (target_offset + 1) state := by
  have hval : (target_offset + 1).val = target_offset.val + 1 :=
    Fin.val_add_one_of_lt' hnext
  intro i hi
  by_cases hlt : i < target_offset
  · exact hinv i hlt
  · have heq : i = target_offset := by
      apply Fin.ext
      simp only [Fin.lt_def] at hi hlt
      omega
    simpa [heq] using hfinal

def Stack.shallowest_copy_position (stack : Stack) (slot : Value) :
    Option (Fin stack.length) :=
  (List.finRange stack.length).reverse.find?
    (fun pos => stack[pos] = slot)

def build_bottom_up
    (target_offset : Fin target.length)
    (state : State source target)
    (hinv : LoopInvariant target_offset state)
    (hsize : state.stack.length ≤ target.length) :
    Except ShuffleErr ((res : Stack) × Trace source res) := do

  -- the offset exists and already holds the slot bound for it: nothing to do
  -- TODO: these checks match the c++, but the first is implied by the second...
  if hskip : target_offset.val < state.stack.length ∧ state.is_final target_offset then

    -- Return when the final target position is reached.
    if hdone : target_offset.val + 1 ≥ target.length
    then return ⟨state.stack, state.trace⟩

    -- increment offset and recurse
    else
      have : NeZero target.length := ⟨by omega⟩
      return ← build_bottom_up (target_offset + 1) state (hinv.advance hskip.2 (by omega)) hsize

  -- all is generated, the final permutation
  if hpending : state.pending_generations = 0 then
    have htarget : ∀ j, (state.mapping.symm j).isSome :=
      (unmapped_target_slots_eq_zero state.mapping).mp (state.hpending.trans hpending)

    let ⟨res, trace⟩ ← permute state.stack (state.mapping.toPermutation hsize htarget)
    return ⟨res, state.trace.concat trace⟩

  -- a target offset that needs something DUPed urgently before it goes out of dup reach
  let mut urgent_to_dup : Option (Fin target.length) := none
  for hmem : offset in [target_offset.val : target.length] do

    -- only offsets no slot is bound for yet (i.e. that need to be duped) can be urgent
    if (state.mapping.symm ⟨offset, hmem.upper⟩).isSome then
      continue

    -- ignore slot kinds that don't need to be duped
    let slot := target[offset]'hmem.upper
    -- TODO: this matches the c++, but is_junk is redundent here (implied by freely generated)
    if hfree : slot.is_junk ∨ slot.can_be_freely_generated ∨ state.spills.is_spilled slot then
      continue

    if let some source_copy := state.stack.shallowest_copy_position slot then
      sorry

    sorry

  sorry
termination_by target.length - target_offset.val
decreasing_by
  have hnext : (target_offset + 1).val = target_offset.val + 1 :=
    Fin.val_add_one_of_lt' (by omega)
  omega

theorem build_bottom_up_correct
    (source target : Stack)
    (target_offset : Fin target.length)
    (state : State source target)
    (hinv : LoopInvariant target_offset state)
    (hsize : state.stack.length ≤ target.length) :
    match build_bottom_up target_offset state hinv hsize with
    | .ok ⟨res, _⟩ => res = target
    | .error _ => True := by
  sorry
