module

public import BbuBridge.Defs
import all BbuBridge.Defs

@[expose] public section

/-!
The unfolding of `buildBottomUp.loop`: past the target, at a final offset, at
the final permutation, and else as the `urgentToDup` scan (`origScan`) followed
by the rest of the body (`origRest`).
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The part of `buildBottomUp.loop` after the `urgentToDup` scan.
def origRest {source target : Stack} {spills : SpillSet} (targetOffset : Nat)
    (state : State source target spills) (urgentToDup : Option Nat) :
    Except ShuffleErr (Result source target spills) := do
  let mut state := state
  if h : urgentToDup.isSome ∧ urgentToDup ≠ some targetOffset ∧
      state.stack.length - targetOffset < MAX_SWAP_DEPTH then
    let ⟨result, _hgen⟩ ← (state.generate (urgentToDup.get h.1)).attach
    if result.blocked.isSome then return result
    state := result.state
    return ← buildBottomUp.loop targetOffset state
  let sourceTop := state.stack.length
  if urgentToDup.isNone ∧ sourceTop > targetOffset ∧ sourceTop < target.length then
    if (state.mapping.positionOf (← index target.length sourceTop)).isNone ∧
        sourceTop - targetOffset < MAX_SWAP_DEPTH then
      let ⟨result, _hgen⟩ ← (state.generate sourceTop).attach
      if result.blocked.isSome then return result
      state := result.state
      return ← buildBottomUp.loop targetOffset state
  if let some boundForTarget := state.mapping.positionOf (← index target.length targetOffset) then
    _ ← requires (boundForTarget ≥ targetOffset) "slot bound for the offset being filled is missing or already below it"
    let sourceForTargetOffset := boundForTarget.val
    let mut pos := sourceForTargetOffset
    if (← slotAt state.stack targetOffset) = (← slotAt state.stack sourceForTargetOffset) then
      pos := targetOffset
    else
      for candidate in
          (List.range state.stack.length).reverse.take (state.depthOf (← index state.stack.length sourceForTargetOffset)) do
        if (← slotAt state.stack candidate) = (← slotAt state.stack sourceForTargetOffset) ∧
            ¬ state.isFinal (← index state.stack.length candidate) then
          pos := candidate
          break
    _ ← requires ((← slotAt state.stack pos) = (← slotAt state.stack sourceForTargetOffset))
      "selected copy differs from the bound slot"
    state ← state.swapDestinations pos sourceForTargetOffset
    if pos = targetOffset then
      return ← buildBottomUp.loop (targetOffset + 1) state
    if pos ≠ state.stack.length - 1 then
      if ¬ (state.isSwapReachable (← index state.stack.length pos)) then
        return ← state.blockSwapUnreachable (← index state.stack.length pos)
      state ← state.swapWith pos
  else
    let result ← state.generate targetOffset
    if result.blocked.isSome then return result
    state := result.state
    if state.isFinal (← index state.stack.length targetOffset) then
      return ← buildBottomUp.loop (targetOffset + 1) state
  _ ← requires (¬ state.isFinal (← index state.stack.length targetOffset)) "target slot is already final"
  if targetOffset ≠ state.stack.length - 1 then
    if ¬ (state.isSwapReachable (← index state.stack.length targetOffset)) then
      return ← state.blockSwapUnreachable (← index state.stack.length targetOffset)
    state ← state.swapWith targetOffset
  return ← buildBottomUp.loop (targetOffset + 1) state

variable {source target : Stack} {spills : SpillSet}

theorem loop_ge (t : Nat) (state : State source target spills) (ht : target.length ≤ t) :
    buildBottomUp.loop t state = .ok ⟨none, state⟩ := by
  rw [buildBottomUp.loop.eq_def]
  simp [ht]; rfl

theorem loop_skip (t : Nat) (state : State source target spills) (ht : t < target.length)
    (hl : t < state.stack.length) (hf : state.isFinal ⟨t, hl⟩) :
    buildBottomUp.loop t state = buildBottomUp.loop (t + 1) state := by
  rw [buildBottomUp.loop.eq_def]
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr ht), ite_eq_left hl,
    show index state.stack.length t = .ok ⟨t, hl⟩ from index_eq ⟨t, hl⟩, except_ok_bind,
    ite_eq_left hf]

theorem loop_finish (t : Nat) (state : State source target spills) (ht : t < target.length)
    (hf : ¬ ∃ h : t < state.stack.length, state.isFinal ⟨t, h⟩) (hp : state.pending_generations = 0) :
    buildBottomUp.loop t state = origFinish state := by
  rw [buildBottomUp.loop.eq_def]
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr ht)]
  by_cases hl : t < state.stack.length
  · have hnf : ¬ state.isFinal ⟨t, hl⟩ := fun h => hf ⟨hl, h⟩
    rw [ite_eq_left hl,
      show index state.stack.length t = .ok ⟨t, hl⟩ from index_eq ⟨t, hl⟩, except_ok_bind,
      ite_eq_right hnf, ite_eq_left hp]
    rfl
  · rw [ite_eq_right hl, ite_eq_left hp]
    rfl

theorem loop_rest (t : Nat) (state : State source target spills) (ht : t < target.length)
    (hf : ¬ ∃ h : t < state.stack.length, state.isFinal ⟨t, h⟩) (hp : state.pending_generations ≠ 0) :
    buildBottomUp.loop t state = origScan state t (origRest t state) := by
  rw [buildBottomUp.loop.eq_def]
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr ht)]
  by_cases hl : t < state.stack.length
  · have hnf : ¬ state.isFinal ⟨t, hl⟩ := fun h => hf ⟨hl, h⟩
    rw [ite_eq_left hl,
      show index state.stack.length t = .ok ⟨t, hl⟩ from index_eq ⟨t, hl⟩, except_ok_bind,
      ite_eq_right hnf, ite_eq_right hp]
    rfl
  · rw [ite_eq_right hl, ite_eq_right hp]
    rfl

-- The check after the loop passes on an error and a block.
theorem post_error (err : ShuffleErr) :
    post (source := source) (target := target) (spills := spills) (.error err) = .error err := rfl

theorem post_blocked (b : Blocked) (state : State source target spills) :
    post (.ok ⟨some b, state⟩) = .ok ⟨some b, state⟩ := rfl

end BbuBridge
