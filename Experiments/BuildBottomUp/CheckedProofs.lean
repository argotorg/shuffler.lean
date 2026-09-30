import Experiments.BuildBottomUp.FiniteExecution

namespace BuildBottomUpExperiments.Checked

-- The public wrapper uses assertion exclusion to recover the original error type.
def restoreResult (result : M α)
    (noAssertion : ∀ reason, result ≠ .error (.assertion reason)) : Except ShuffleErr α :=
  match result with
  | .ok value => .ok value
  | .error (.blocked excess) => .error (.Blocked excess)
  | .error (.assertion reason) => False.elim (noAssertion reason rfl)

theorem restoreResult_eq (result : M α)
    (noAssertion : ∀ reason, result ≠ .error (.assertion reason)) :
    liftResult (restoreResult result noAssertion) = result := by
  cases result with
  | ok value => rfl
  | error err =>
    cases err with
    | blocked excess => rfl
    | assertion reason => exact False.elim (noAssertion reason rfl)

-- Equality here includes the complete state, mapping, and trace.
theorem push_eq (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hbound : state.mapping.symm dest = none) :
    push state slot dest = .ok (state.push slot dest hgen hbound) := by
  cases slot <;> simp [push, requires, State.push, hbound, hgen,
    pure, Except.pure, bind, Except.bind]

theorem dup_eq (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.is_dup_reachable copy)
    (hbound : state.mapping.symm dest = none) :
    dup state copy dest = .ok (state.dup copy dest hdup hbound) := by
  simp [dup, requires, State.dup, hbound, hdup, pure, Except.pure, bind, Except.bind]

theorem swapWith_eq (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.is_swap_reachable pos)
    (hnfinal : ¬ state.is_final pos.val) :
    swapWith state pos.val = .ok (state.swapWith pos hbelow hreach hnfinal) := by
  simp [swapWith, requires, State.swapWith, index, pos.isLt, bind, Except.bind,
    pure, Except.pure, hbelow, hreach, hnfinal]
  split
  rfl

theorem produce_eq (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.is_available dest) :
    produce state dest = liftResult (state.produce dest hbound havailable) := by
  by_cases hjunk : target[dest.val].is_junk
  · have hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val] :=
      Or.inl (target[dest.val].can_be_freely_generated_of_is_junk hjunk)
    simp +instances [produce, State.produce, hbound, hjunk, push_eq state _ dest hgen hbound,
      ensure, requires, positionOf, dest.isLt, State.push,
      liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
  · cases hcopy : state.stack.shallowest_copy_position target[dest.val] with
    | none =>
      have hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val] := by
        simpa [State.is_available, hcopy] using havailable
      simp +instances [produce, State.produce, hbound, hjunk, hcopy, hgen,
        push_eq state _ dest hgen hbound,
        ensure, requires, positionOf, dest.isLt, State.push,
        liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
    | some copy =>
      by_cases hdup : state.stack.is_dup_reachable copy
      · simp +instances [produce, State.produce, hbound, hjunk, hcopy, hdup,
          dup_eq state copy dest hdup hbound,
          ensure, requires, positionOf, dest.isLt, State.dup,
          liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
      · by_cases hgen : target[dest.val].can_be_freely_generated ∨ spills.is_spilled target[dest.val]
        · simp +instances [produce, State.produce, hbound, hjunk, hcopy, hdup, hgen,
            push_eq state _ dest hgen hbound,
            ensure, requires, positionOf, dest.isLt, State.push,
            liftResult, Except.mapError, pure, Except.pure, bind, Except.bind]
        · simp [produce, State.produce, hbound, hjunk, hcopy, hdup, hgen,
            liftResult, Except.mapError,
            pure, Except.pure, bind, Except.bind, throw, throwThe]
          rfl

theorem generate_eq (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.is_available dest) :
    generate state dest.val = liftResult (state.generate dest hbound havailable) := by
  simp only [generate, index, dest.isLt, ↓reduceDIte, pure_bind]
  rw [produce_eq state dest hbound havailable]
  unfold State.generate
  cases hresult : state.produce dest hbound havailable with
  | error err => cases err; rfl
  | ok next =>
    simp only [liftResult, Except.mapError, bind, Except.bind]
    by_cases hswap : dest.val + 1 < next.stack.length ∧ ¬ next.is_final dest.val
    · let pos : Fin next.stack.length := ⟨dest.val, by omega⟩
      by_cases hequal : next.stack[dest.val] = next.stack.getLast (by intro h; simp [h] at hswap)
      · have htop : next.stack.length - 1 < next.stack.length := by omega
        simp [hswap, hequal, pos, swapDestinations, index, pos.isLt, htop,
          bind, Except.bind, pure, Except.pure]
      · by_cases hreach : next.stack.is_swap_reachable pos
        · simp [hswap, hequal, pos, hreach, swapWith_eq next pos hswap.1 hreach hswap.2,
            pure, Except.pure]
        · simp [hswap, hequal, pos, hreach, pure, Except.pure]
    · simp [hswap, pure, Except.pure]

theorem generate_spec (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ)
    (inv : BuildBottomUpInvariant cursor state) (hbound : state.mapping.symm dest = none) :
    match generate state dest.val with
    | .ok next => BuildBottomUpInvariant cursor next ∧
        next.pending_generations < state.pending_generations ∧ (positionOf next dest.val).isSome
    | .error err => ∃ excess, err = .blocked excess := by
  rw [generate_eq state dest hbound (inv.available dest)]
  cases hresult : state.generate dest hbound (inv.available dest) with
  | error err =>
    cases err with
    | Blocked excess =>
      exact ⟨excess, rfl⟩
  | ok next =>
    have hp := state.generate_preserves cursor dest inv.processed inv.size inv.pending
      inv.available hbound hresult
    have hinv : BuildBottomUpInvariant cursor next := inv.generate dest hbound hresult
    refine ⟨hinv, hp.2.2.2.2, ?_⟩
    rcases state.generate_position dest hbound (inv.available dest) hresult with hfinal | htop
    · have hposition : positionOf next dest.val = some dest.val := by
        simpa [positionOf, State.is_final, dest.isLt] using hfinal
      simp [hposition]
    · simp [positionOf, dest.isLt, htop]

-- A loop over the checked helper, with its proof outside the body.
def generateUntilBound (state : State source target spills) (dest : Fin target.length) :
    M (State source target spills) := do
  let mut state := state
  while (positionOf state dest.val).isNone do
    state ← generate state dest.val
  return state

theorem generateUntilBound_unfold (state : State source target spills) (dest : Fin target.length) :
    generateUntilBound state dest =
      if (positionOf state dest.val).isNone then do
        let next ← generate state dest.val
        generateUntilBound next dest
      else pure state := by
  unfold generateUntilBound
  dsimp only
  conv_lhs => rw [loop_unfold]
  split <;> simp_all

-- Generation binds the destination, so this loop takes at most one iteration.
theorem generateUntilBound_eq (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ) (inv : BuildBottomUpInvariant cursor state) :
    generateUntilBound state dest =
      if (positionOf state dest.val).isNone then generate state dest.val else .ok state := by
  rw [generateUntilBound_unfold]
  split
  · rename_i hnone
    have hbound : state.mapping.symm dest = none := by
      simpa [positionOf, dest.isLt] using hnone
    have hspec := generate_spec state dest cursor inv hbound
    cases hresult : generate state dest.val with
    | error err => rfl
    | ok next =>
      simp only [hresult] at hspec
      simp only [bind, Except.bind]
      rw [generateUntilBound_unfold]
      simp [Option.isSome_iff_ne_none.mp hspec.2.2, pure, Except.pure]
  · rfl

theorem generateUntilBound_spec (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ) (inv : BuildBottomUpInvariant cursor state) :
    match generateUntilBound state dest with
    | .ok next => BuildBottomUpInvariant cursor next ∧ (positionOf next dest.val).isSome
    | .error err => ∃ excess, err = .blocked excess := by
  rw [generateUntilBound_eq state dest cursor inv]
  by_cases hnone : (positionOf state dest.val).isNone = true
  · rw [ite_eq_left hnone]
    have hbound : state.mapping.symm dest = none := by
      simpa [positionOf, dest.isLt] using hnone
    have hspec := generate_spec state dest cursor inv hbound
    cases hresult : generate state dest.val with
    | error err => simpa [hresult] using hspec
    | ok next =>
      simp only [hresult] at hspec
      exact ⟨hspec.1, hspec.2.2⟩
  · rw [ite_eq_right hnone]
    exact ⟨inv, Option.isSome_iff_ne_none.mpr (by simpa using hnone)⟩

/-- info: 'BuildBottomUpExperiments.Checked.generateUntilBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generateUntilBound_spec

end BuildBottomUpExperiments.Checked
