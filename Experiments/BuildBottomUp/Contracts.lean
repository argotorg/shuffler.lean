import Experiments.BuildBottomUp.ActionProofs

namespace BuildBottomUpExperiments.Checked

-- A blocked operation is allowed. An assertion error is excluded.
def Spec (result : M α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error (.blocked _) => True
  | .error (.assertion _) => False

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
