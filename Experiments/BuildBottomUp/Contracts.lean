import Experiments.BuildBottomUp.ActionProofs
import Std.Internal.Do
import Std.Tactic.Do

open Std.Internal.Do

set_option mvcgen.warning false

namespace BuildBottomUpExperiments.Checked

-- A blocked operation is allowed. An assertion error is excluded.
def Spec (result : M α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error (.blocked _) => True
  | .error (.assertion _) => False

-- The standard contracts use the same error policy as the result-level API.
def allowedErrors : EPost⟨Error → Prop⟩ :=
  epost⟨fun | .blocked _ => True | .assertion _ => False⟩

theorem spec_iff_triple (result : M α) (post : α → Prop) :
    Spec result post ↔ ⦃True⦄ result ⦃post; allowedErrors⦄ := by
  cases result with
  | ok value => exact ⟨fun h => ⟨fun _ => h⟩, fun h => h.le_wp trivial⟩
  | error err => cases err <;> exact ⟨fun h => ⟨fun _ => h⟩, fun h => h.le_wp trivial⟩

theorem action_triple_iff (action : Action source target spills α)
    (state : State source target spills) (post : α → State source target spills → Prop) :
    (⦃fun s => s = state⦄ action ⦃post; allowedErrors⦄) ↔
      Spec (action.run state) (fun r => post r.1 r.2) := by
  constructor
  · intro h
    exact (spec_iff_triple _ _).mpr ⟨fun _ => h.le_wp state rfl⟩
  · intro h
    exact ⟨fun s hs => by subst s; exact ((spec_iff_triple _ _).mp h).le_wp trivial⟩

theorem Spec.of_action {action : Action source target spills Unit}
    {state : State source target spills} {post : State source target spills → Prop}
    (h : ⦃fun s => s = state⦄ action ⦃fun _ s => post s; allowedErrors⦄) :
    Spec (action.exec state) post := by
  have hp : Spec (action.run state) (fun r => post r.2) :=
    (spec_iff_triple _ _).mpr ⟨fun _ => h.le_wp state rfl⟩
  cases heq : action.run state with
  | ok result => simpa [Action.exec, heq, Spec] using hp
  | error err => cases err <;> simp_all [Action.exec, Spec]

@[spec] theorem requires_spec (condition : Prop) [Decidable condition] (reason : String) :
    ⦃condition⦄ requires condition reason ⦃fun _ => True; allowedErrors⦄ := by
  vcgen [requires] with finish

@[spec] theorem ensure_spec (condition : Prop) [Decidable condition] (reason : String) :
    ⦃condition⦄ ensure condition reason ⦃fun _ => True; allowedErrors⦄ := by
  vcgen [ensure] with finish

@[spec] theorem index_spec (size offset : ℕ) :
    ⦃offset < size⦄ index size offset ⦃fun i => i.val = offset; allowedErrors⦄ := by
  vcgen [index] with finish

@[spec] theorem slotAt_spec (stack : Stack) (offset : ℕ) (h : offset < stack.length) :
    ⦃True⦄ slotAt stack offset ⦃fun slot => slot = stack[offset]; allowedErrors⦄ := by
  vcgen [slotAt] with finish

@[spec] theorem liftResult_spec (result : Except ShuffleErr α) :
    ⦃True⦄ liftResult result ⦃fun _ => True; allowedErrors⦄ := by
  cases result with
  | ok value => exact ⟨fun _ => trivial⟩
  | error err => cases err; exact ⟨fun _ => trivial⟩

@[spec] theorem swapDestinations_spec (state : State source target spills)
    (a b : ℕ) (ha : a < state.stack.length) (hb : b < state.stack.length) :
    ⦃fun s => s = state⦄ swapDestinations a b
    ⦃fun _ s => s = { state with mapping := state.mapping.swapDestinations ⟨a, ha⟩ ⟨b, hb⟩ }; allowedErrors⦄ := by
  vcgen [swapDestinations, index] <;> subst_vars <;> simp_all

theorem Spec.bind {result : M α} {pre : α → Prop} {next : α → M β}
    {post : β → Prop} (h : Spec result pre)
    (step : ∀ value, pre value → Spec (next value) post) :
    Spec (result >>= next) post := by
  cases result with
  | ok value => exact step value h
  | error err => cases err <;> exact h

theorem Spec.mono {result : M α} {pre post : α → Prop}
    (h : Spec result pre) (step : ∀ value, pre value → post value) : Spec result post := by
  cases result with
  | ok value => exact step value h
  | error err => cases err <;> exact h

theorem Spec.noAssertion {result : M α} {post : α → Prop}
    (h : Spec result post) (reason : String) : result ≠ .error (.assertion reason) := by
  intro heq
  simp [heq, Spec] at h

theorem Spec.error {result : M α} {post : α → Prop}
    (h : Spec result post) (heq : result = .error err) : ∃ excess, err = .blocked excess := by
  cases err with
  | blocked excess => exact ⟨excess, rfl⟩
  | assertion reason => exact (h.noAssertion reason heq).elim

@[simp] theorem spec_ok (value : α) (post : α → Prop) : Spec (.ok value) post ↔ post value := Iff.rfl
@[simp] theorem spec_blocked (excess : ℕ) (post : α → Prop) : Spec (.error (.blocked excess)) post := trivial

theorem ensure_of_true (condition : Prop) [Decidable condition] (h : condition) (reason : String) :
    ensure condition reason = .ok () := by
  simp [ensure, requires, h, pure, Except.pure, bind, Except.bind]

@[simp] theorem index_eq (i : Fin size) : index size i.val = .ok i := by
  simp [index, i.isLt, pure, Except.pure]

@[simp] theorem slotAt_index (stack : Stack) (i : Fin stack.length) :
    slotAt stack i.val = .ok stack[i] := by simp [slotAt, index_eq]

theorem swapDestinations_result (state : State source target spills)
    (a b : Fin state.stack.length) :
    (swapDestinations a.val b.val).exec state =
      .ok { state with mapping := state.mapping.swapDestinations a b } := by
  simp only [swapDestinations, Action.exec_get, Action.exec_lift, Action.exec_set,
    index_eq]
  rfl

end BuildBottomUpExperiments.Checked
