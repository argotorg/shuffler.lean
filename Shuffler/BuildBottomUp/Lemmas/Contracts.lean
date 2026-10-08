import Shuffler.BuildBottomUp.Defs
import Std.Tactic.Do

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

theorem except_ok_bind (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

theorem except_error_bind (err : ε) (next : α → Except ε β) :
    (Except.error err >>= next) = .error err := rfl

-- A blocked operation is allowed. An assertion error is excluded.
def Spec (result : Except Error α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error (.blocked _) => True
  | .error (.assertion _) => False

def allowedErrors : EPost⟨Error → Prop⟩ :=
  epost⟨fun | .blocked _ => True | .assertion _ => False⟩

theorem spec_iff_triple (result : Except Error α) (post : α → Prop) :
    Spec result post ↔ ⦃True⦄ result ⦃post; allowedErrors⦄ := by
  cases result with
  | ok value => exact ⟨fun h => ⟨fun _ => h⟩, fun h => h.le_wp trivial⟩
  | error err => cases err <;> exact ⟨fun h => ⟨fun _ => h⟩, fun h => h.le_wp trivial⟩

@[spec] theorem requires_spec (condition : Prop) [Decidable condition] (reason : String) :
    ⦃condition⦄ requires condition reason ⦃fun _ => True; allowedErrors⦄ := by
  vcgen [requires] with finish

@[spec] theorem index_spec (size offset : ℕ) :
    ⦃offset < size⦄ index size offset ⦃fun i => i.val = offset; allowedErrors⦄ := by
  vcgen [index] with finish

@[spec] theorem slotAt_spec (stack : Stack) (offset : ℕ) (h : offset < stack.length) :
    ⦃True⦄ slotAt stack offset ⦃fun slot => slot = stack[offset]; allowedErrors⦄ := by
  vcgen [slotAt] with finish

@[spec] theorem swapDestinations_spec (state : State source target spills)
    (a b : ℕ) (ha : a < state.stack.length) (hb : b < state.stack.length) :
    ⦃True⦄ state.swapDestinations a b
    ⦃fun s => s = { state with mapping := state.mapping.swapDestinations ⟨a, ha⟩ ⟨b, hb⟩ }; allowedErrors⦄ := by
  vcgen [State.swapDestinations, index] <;> simp_all

theorem Spec.bind {result : Except Error α} {pre : α → Prop} {next : α → Except Error β}
    {post : β → Prop} (h : Spec result pre)
    (step : ∀ value, pre value → Spec (next value) post) :
    Spec (result >>= next) post := by
  cases result with
  | ok value => exact step value h
  | error err => cases err <;> exact h

theorem Spec.mono {result : Except Error α} {pre post : α → Prop}
    (h : Spec result pre) (step : ∀ value, pre value → post value) : Spec result post := by
  cases result with
  | ok value => exact step value h
  | error err => cases err <;> exact h

theorem Spec.noAssertion {result : Except Error α} {post : α → Prop}
    (h : Spec result post) (reason : String) : result ≠ .error (.assertion reason) := by
  intro heq
  simp [heq, Spec] at h

theorem Spec.error {result : Except Error α} {post : α → Prop}
    (h : Spec result post) (heq : result = .error err) : ∃ excess, err = .blocked excess := by
  cases err with
  | blocked excess => exact ⟨excess, rfl⟩
  | assertion reason => exact (h.noAssertion reason heq).elim

@[simp] theorem spec_ok (value : α) (post : α → Prop) : Spec (.ok value) post ↔ post value := Iff.rfl
@[simp] theorem spec_blocked (excess : ℕ) (post : α → Prop) : Spec (.error (.blocked excess)) post := trivial

theorem requires_of_true (condition : Prop) [Decidable condition] (h : condition) (reason : String) :
    requires condition reason = .ok ⟨h⟩ := by
  simp [requires, h, pure, Except.pure]

@[simp] theorem index_eq (i : Fin size) : index size i.val = .ok i := by
  simp [index, i.isLt, pure, Except.pure]

@[simp] theorem slotAt_index (stack : Stack) (i : Fin stack.length) :
    slotAt stack i.val = .ok stack[i] := by simp [slotAt, index_eq]

-- Finality over any target offset. `isFinal` is the same fact for an offset on the stack.
def State.IsFinal (state : State source target spills) (offset : ℕ) : Prop :=
  if h : offset < target.length then
    (state.mapping.symm ⟨offset, h⟩).map Fin.val = some offset
  else False

instance (state : State source target spills) (offset : ℕ) : Decidable (state.IsFinal offset) :=
  by unfold State.IsFinal; infer_instance

@[simp] theorem State.isFinal_iff (state : State source target spills) (i : Fin state.stack.length) :
    state.isFinal i ↔ state.IsFinal i.val := by
  simp only [State.isFinal, State.destinationOf, State.IsFinal, Option.map_eq_some_iff]
  constructor
  · rintro ⟨d, hd, hval⟩
    have hlt : i.val < target.length := hval ▸ d.isLt
    simp only [hlt, ↓reduceDIte]
    refine ⟨i, ?_, rfl⟩
    rw [PEquiv.eq_some_iff, hd]
    exact congrArg some (Fin.ext hval)
  · intro h
    split_ifs at h with hlt
    obtain ⟨j, hj, hval⟩ := h
    obtain rfl : j = i := Fin.ext hval
    exact ⟨_, (PEquiv.eq_some_iff _).mp hj, rfl⟩

theorem swapDestinations_result (state : State source target spills)
    (a b : Fin state.stack.length) :
    state.swapDestinations a.val b.val =
      .ok { state with mapping := state.mapping.swapDestinations a b } := by
  simp only [State.swapDestinations, index_eq]
  rfl

end Shuffler.BuildBottomUp
