import Experiments.BuildBottomUp.Checked

namespace BuildBottomUpExperiments.Checked
open Std.Do

-- Use this at the public boundary once the full loop's assertion-exclusion
-- theorem exists. The proof removes the extra cases without inventing a result.
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

-- Equality here includes the complete state and trace, or the Blocked error.
theorem generate_eq (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.is_available dest) :
    generate state dest.val = liftResult (state.generate dest hbound havailable) := by
  simp [generate, index, dest.isLt, bind, Except.bind, hbound, havailable]

theorem swapWith_eq (state : State source target spills) (pos : Fin state.stack.length)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.is_swap_reachable pos)
    (hnfinal : ¬ state.is_final pos.val) :
    swapWith state pos.val = .ok (state.swapWith pos hbelow hreach hnfinal) := by
  simp [swapWith, index, pos.isLt, bind, Except.bind, pure, Except.pure, hbelow, hreach, hnfinal]

theorem generate_spec (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ) :
    ⦃⌜BuildBottomUpInvariant cursor state ∧ state.mapping.symm dest = none⌝⦄
      generate state dest.val
    ⦃post⟨fun next => ⌜BuildBottomUpInvariant cursor next ∧
          next.pending_generations < state.pending_generations⌝,
        fun err => ⌜∃ excess, err = .blocked excess⌝⟩⦄ := by
  mintro ⟨inv, hbound⟩
  rw [generate_eq state dest hbound (inv.available dest)]
  cases hresult : state.generate dest hbound (inv.available dest) with
  | error err =>
    cases err with
    | Blocked excess =>
      simp only [liftResult, Except.mapError]
      mvcgen
      exact ⟨excess, rfl⟩
  | ok next =>
    have hp := state.generate_preserves cursor dest inv.processed inv.size inv.pending
      inv.available hbound hresult
    have hinv : BuildBottomUpInvariant cursor next := inv.generate dest hbound hresult
    simp only [liftResult, Except.mapError]
    mvcgen
    exact ⟨hinv, hp.2.2.2.2⟩

-- Probe the while rule on actual checked generation, with its proof outside the body.
def generateUntilBound (state : State source target spills) (dest : Fin target.length) :
    M (State source target spills) := do
  let mut state := state
  while (positionOf state dest.val).isNone do
    state ← generate state dest.val
  return state

-- The theorem proves termination, invariant preservation, a bound destination,
-- and exclusion of assertion errors. The only admitted failure is Blocked.
theorem generateUntilBound_spec (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ) :
    ⦃⌜BuildBottomUpInvariant cursor state⌝⦄ generateUntilBound state dest
    ⦃post⟨fun next => ⌜BuildBottomUpInvariant cursor next ∧ (positionOf next dest.val).isSome⌝,
        fun err => ⌜∃ excess, err = .blocked excess⌝⟩⦄ := by
  have step_spec (st : State source target spills) := generate_spec st dest cursor
  mvcgen [generateUntilBound, step_spec] invariants
  | inv1 => fun s => ⟨s.pending_generations⟩
  | inv2 => post⟨fun s => match s with
      | .inl st => ⌜BuildBottomUpInvariant cursor st⌝
      | .inr st => ⌜BuildBottomUpInvariant cursor st ∧ (positionOf st dest.val).isSome⌝,
      fun err => ⌜∃ excess, err = .blocked excess⌝⟩
  all_goals simp_all [WhileVariant.eval, SVal.evalsTo, positionOf, dest.isLt,
    Option.isSome_iff_ne_none]

/-- info: 'BuildBottomUpExperiments.Checked.generateUntilBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generateUntilBound_spec

end BuildBottomUpExperiments.Checked
