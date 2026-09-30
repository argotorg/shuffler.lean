import Experiments.BuildBottomUp.FiniteExecution
import Experiments.BuildBottomUp.HelperProofs

open Std.Internal.Do

set_option mvcgen.warning false

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

theorem generate_spec (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ)
    (inv : Invariant cursor state) (hbound : state.mapping.symm dest = none) :
    match (generate dest.val).exec state with
    | .ok next => Invariant cursor next ∧
        next.pending_generations < state.pending_generations ∧ (positionOf next dest.val).isSome
    | .error err => ∃ excess, err = .blocked excess := by
  have h := generate_contract state dest hbound (inv.available dest)
  cases heq : (generate dest.val).exec state with
  | error err => exact h.error heq
  | ok next =>
    have hg : Generation state next dest := by simpa only [heq, Spec] using h
    refine ⟨hg.invariant inv, hg.decreases inv, ?_⟩
    rcases hg.position with hf | ht
    · have hf' : positionOf next dest.val = some dest.val := by
        simpa [positionOf, State.isFinal, dest.isLt] using hf
      simp [hf']
    · simp [positionOf, dest.isLt, ht]

-- A loop over the checked helper, with its proof outside the body.
def generateUntilBound (dest : Fin target.length) : Action source target spills Unit := do
  while (positionOf (← get) dest.val).isNone do
    generate dest.val

theorem generateUntilBound_triple (dest : Fin target.length) (cursor : ℕ) :
    ⦃Invariant cursor⦄ (generateUntilBound dest : Action source target spills Unit)
    ⦃fun _ state => Invariant cursor state ∧ (positionOf state dest.val).isSome; allowedErrors⦄ := by
  vcgen [generateUntilBound] invariants
  · RepeatInvariant.ofInvariantAndBreak (fun _ state => Invariant cursor state)
      (fun _ state => (positionOf state dest.val).isSome)
  · RepeatVariant.ofMeasure (fun _ (state : State source target spills) => state.pending_generations)
  all_goals try simp_all [positionOf, dest.isLt, Option.isSome_iff_ne_none]
  case vc3 hgen =>
    obtain ⟨rfl, hi⟩ := (by assumption : _ ∧ Invariant cursor _)
    exact ⟨hgen.decreases hi, hgen.invariant hi⟩
  case vc5 => exact Invariant.available (by tauto) dest

theorem generateUntilBound_unfold (state : State source target spills) (dest : Fin target.length) :
    (generateUntilBound dest).exec state =
      if (positionOf state dest.val).isNone then do
        let next ← (generate dest.val).exec state
        (generateUntilBound dest).exec next
      else pure state := by
  unfold generateUntilBound
  conv_lhs => rw [loop_unfold]
  simp only [Action.exec, StateT.run_bind, StateT.run_get,
    StateT.run_pure, bind_assoc, pure_bind]
  split
  · simp only [Action.run_bind_update, StateT.run_pure, Action.exec, bind_assoc, pure_bind]
  · rfl

-- Generation binds the destination, so this loop takes at most one iteration.
theorem generateUntilBound_eq (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ) (inv : Invariant cursor state) :
    (generateUntilBound dest).exec state =
      if (positionOf state dest.val).isNone then (generate dest.val).exec state else .ok state := by
  rw [generateUntilBound_unfold]
  split
  · rename_i hnone
    have hbound : state.mapping.symm dest = none := by
      simpa [positionOf, dest.isLt] using hnone
    have hspec := generate_spec state dest cursor inv hbound
    cases hresult : (generate dest.val).exec state with
    | error err => rfl
    | ok next =>
      simp only [hresult] at hspec
      simp only [bind, Except.bind]
      rw [generateUntilBound_unfold]
      simp [Option.isSome_iff_ne_none.mp hspec.2.2, pure, Except.pure]
  · rfl

theorem generateUntilBound_spec (state : State source target spills)
    (dest : Fin target.length) (cursor : ℕ) (inv : Invariant cursor state) :
    match (generateUntilBound dest).exec state with
    | .ok next => Invariant cursor next ∧ (positionOf next dest.val).isSome
    | .error err => ∃ excess, err = .blocked excess := by
  have h : Spec ((generateUntilBound dest).exec state)
      (fun next => Invariant cursor next ∧ (positionOf next dest.val).isSome) :=
    Spec.of_action ⟨fun s hs => by subst s; exact (generateUntilBound_triple dest cursor).le_wp state inv⟩
  cases heq : (generateUntilBound dest).exec state with
  | error err => exact h.error heq
  | ok next => simpa only [heq, Spec] using h

/-- info: 'BuildBottomUpExperiments.Checked.generateUntilBound_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generateUntilBound_spec

end BuildBottomUpExperiments.Checked
