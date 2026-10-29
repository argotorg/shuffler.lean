module

public import Shuffler.Emission.Defs
public import Std.WP.Monad.Instances
public import Std.WP.Triple.Basic
public import Shuffler.Util
import Batteries.Data.Except
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP

set_option experimental.vcgen true

namespace Shuffler.Emission

@[simp] theorem completed_ok (state : State source target spills) :
    (((.ok ⟨none, state⟩) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = .ok state := rfl

@[simp] theorem completed_blocked (state : State source target spills) (blocked : Blocked) :
    (((.ok ⟨some blocked, state⟩) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = .error (.Blocked blocked) := rfl

@[simp] theorem completed_error (err : ShuffleErr) :
    (((.error err : Except ShuffleErr (Result source target spills)) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = .error err := rfl

@[simp] theorem completedTrace_ok (state : State source target spills) :
    ((((.ok ⟨none, state⟩) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = .ok ⟨state.stack, state.trace⟩ := rfl

@[simp] theorem completedTrace_blocked (state : State source target spills) (blocked : Blocked) :
    ((((.ok ⟨some blocked, state⟩) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = .error (.Blocked blocked) := rfl

@[simp] theorem completedTrace_error (err : ShuffleErr) :
    ((((.error err : Except ShuffleErr (Result source target spills)) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = .error err := rfl

@[simp] theorem completed_bind (x : Except ShuffleErr α)
    (f : α → Except ShuffleErr (Result source target spills)) :
    (((x >>= f) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = x >>= (fun a => (((f a) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
          if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state)) := by
  cases x <;> rfl

@[simp] theorem completedTrace_bind (x : Except ShuffleErr α)
    (f : α → Except ShuffleErr (Result source target spills)) :
    ((((x >>= f) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = x >>= (fun a => ((((f a) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
        pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack))) := by
  cases x <;> rfl

theorem completed_continue (run : Except ShuffleErr (Result source target spills))
    (next : Result source target spills → Except ShuffleErr (Result source target spills)) :
    (run >>= fun r => (((if r.blocked.isSome then pure r else next r) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state)) =
      (((run : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state => (((next ⟨none, state⟩) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
            if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state)) := by
  cases run with
  | error err => rfl
  | ok r => cases r with
    | mk blocked state => cases blocked <;> rfl

@[simp] theorem completed_ite (p : Prop) [Decidable p]
    (a b : Except ShuffleErr (Result source target spills)) :
    (((if p then a else b) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = if p then ((a : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
          if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) else ((b : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
          if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) := by
  split <;> rfl

theorem completed_ok_inversion {run : Except ShuffleErr (Result source target spills)}
    {state : State source target spills} (h : ((run : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) = .ok state) :
    run = .ok ⟨none, state⟩ := by
  cases run with
  | error err => cases h
  | ok r => cases r with
    | mk blocked current => cases blocked with
      | some blocked => cases h
      | none => cases h; rfl

theorem completedTrace_guard (run : Except ShuffleErr (Result source target spills))
    (next : Result source target spills → Except ShuffleErr ((stack : Stack) × Trace spills source stack)) :
    (run >>= fun r => if r.blocked.isSome then ((((pure r) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) else next r) =
      (((run : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state => next ⟨none, state⟩) := by
  cases run with
  | error err => rfl
  | ok r => cases r with
    | mk blocked state => cases blocked <;> rfl

theorem completedTrace_attach_guard (run : Except ShuffleErr (Result source target spills))
    (next : {r // run = .ok r} → Except ShuffleErr ((stack : Stack) × Trace spills source stack)) :
    (run.attach >>= fun r => if r.val.blocked.isSome then ((((pure r.val) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) else next r) =
      ((((run : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state)).attach >>= fun state =>
        next ⟨⟨none, state.val⟩, completed_ok_inversion state.property⟩) := by
  cases run with
  | error err => rfl
  | ok r => cases r with
    | mk blocked state => cases blocked <;> rfl

@[simp] theorem completedTrace_ite (p : Prop) [Decidable p]
    (a b : Except ShuffleErr (Result source target spills)) :
    ((((if p then a else b) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) =
      if p then (((a : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
        pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) else (((b : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
          if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
          pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) := by
  split <;> rfl

@[simp] theorem completedTrace_dite (p : Prop) [Decidable p]
    (a : p → Except ShuffleErr (Result source target spills))
    (b : ¬p → Except ShuffleErr (Result source target spills)) :
    ((((if h : p then a h else b h) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) =
      if h : p then ((((a h) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
        if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
        pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) else ((((b h) : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
          if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
          pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) := by
  split <;> rfl

-- Relate the proof projection to the result returned by the algorithm.
theorem completedTrace_of_ok {run : Except ShuffleErr (Result source target spills)}
    {state : State source target spills} (h : run = .ok ⟨none, state⟩) :
    (((run : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = .ok ⟨state.stack, state.trace⟩ := by
  rw [h]
  rfl

theorem completedTrace_ok_inversion {run : Except ShuffleErr (Result source target spills)}
    {value : (stack : Stack) × Trace spills source stack}
    (h : (((run : Except ShuffleErr (Result _ _ _)) >>= fun (r : Result _ _ _) =>
      if h : r.blocked.isSome then throw (.Blocked (r.blocked.get h)) else pure r.state) >>= fun state =>
      pure (⟨state.stack, state.trace⟩ : (stack : Stack) × Trace _ _ stack)) = .ok value) :
    ∃ state, run = .ok ⟨none, state⟩ ∧ ⟨state.stack, state.trace⟩ = value := by
  cases run with
  | error err => cases h
  | ok r => cases r with
    | mk blocked state => cases blocked with
      | some blocked => cases h
      | none => exact ⟨state, rfl, Except.ok.inj h⟩

-- A blocked operation is allowed. An assertion error is excluded.
def Spec (result : Except ShuffleErr α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error (.Blocked _) => True
  | .error (.assertion _) => False

def allowedErrors : ShuffleErr → Prop :=
  fun | .Blocked _ => True | .assertion _ => False

theorem spec_iff_triple (result : Except ShuffleErr α) (post : α → Prop) :
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

theorem block_eq (state : State source target spills) (pos : Fin state.stack.length)
    (excess : ℕ) (h : excess > 0) :
    state.block pos excess = .ok ⟨some ⟨pos.val, excess⟩, state⟩ := by
  simp [State.block, requires, h, pure, Except.pure, bind, Except.bind]

theorem blockSwapUnreachable_eq (state : State source target spills)
    (pos : Fin state.stack.length) (h : ¬ state.isSwapReachable pos) :
    state.blockSwapUnreachable pos =
      .ok ⟨some ⟨pos.val, (state.depthOf pos).val - MAX_SWAP_DEPTH⟩, state⟩ := by
  apply block_eq
  simp only [State.isSwapReachable] at h
  omega

theorem blockDupUnreachable_eq (state : State source target spills)
    (pos : Fin state.stack.length) (h : ¬ state.stack.isDupReachable pos) :
    state.blockDupUnreachable pos =
      .ok ⟨some ⟨pos.val, (state.depthOf pos).val - MAX_DUP_DEPTH⟩, state⟩ := by
  apply block_eq
  simp only [Stack.isDupReachable, State.depthOf] at *
  omega

@[spec] theorem blockSwapUnreachable_spec (state : State source target spills)
    (pos : Fin state.stack.length) :
    ⦃¬ state.isSwapReachable pos⦄ state.blockSwapUnreachable pos
    ⦃fun result => result = ⟨some ⟨pos.val, (state.depthOf pos).val - MAX_SWAP_DEPTH⟩, state⟩;
      allowedErrors⦄ := by
  refine ⟨fun h => ?_⟩
  rw [blockSwapUnreachable_eq state pos h]
  trivial

@[spec] theorem blockDupUnreachable_spec (state : State source target spills)
    (pos : Fin state.stack.length) :
    ⦃¬ state.stack.isDupReachable pos⦄ state.blockDupUnreachable pos
    ⦃fun result => result = ⟨some ⟨pos.val, (state.depthOf pos).val - MAX_DUP_DEPTH⟩, state⟩;
      allowedErrors⦄ := by
  refine ⟨fun h => ?_⟩
  rw [blockDupUnreachable_eq state pos h]
  trivial

@[spec] theorem swapDestinations_spec (state : State source target spills)
    (a b : ℕ) (ha : a < state.stack.length) (hb : b < state.stack.length) :
    ⦃True⦄ state.swapDestinations a b
    ⦃fun s => s = { state with mapping := state.mapping.swapDestinations ⟨a, ha⟩ ⟨b, hb⟩ }; allowedErrors⦄ := by
  vcgen [State.swapDestinations, index] <;> simp_all

theorem Spec.bind {result : Except ShuffleErr α} {pre : α → Prop} {next : α → Except ShuffleErr β}
    {post : β → Prop} (h : Spec result pre)
    (step : ∀ value, pre value → Spec (next value) post) :
    Spec (result >>= next) post := by
  cases result with
  | ok value => exact step value h
  | error err => cases err <;> exact h

theorem Spec.mono {result : Except ShuffleErr α} {pre post : α → Prop}
    (h : Spec result pre) (step : ∀ value, pre value → post value) : Spec result post := by
  cases result with
  | ok value => exact step value h
  | error err => cases err <;> exact h

theorem Spec.noAssertion {result : Except ShuffleErr α} {post : α → Prop}
    (h : Spec result post) (reason : String) : result ≠ .error (.assertion reason) := by
  intro heq
  simp [heq, Spec] at h

theorem Spec.error {result : Except ShuffleErr α} {post : α → Prop}
    (h : Spec result post) (heq : result = .error err) : ∃ blocked, err = .Blocked blocked := by
  cases err with
  | Blocked blocked => exact ⟨blocked, rfl⟩
  | assertion reason => exact (h.noAssertion reason heq).elim

@[simp] theorem spec_ok (value : α) (post : α → Prop) : Spec (.ok value) post ↔ post value := Iff.rfl
@[simp] theorem spec_blocked (blocked : Blocked) (post : α → Prop) : Spec (.error (.Blocked blocked)) post := trivial

@[simp] theorem index_eq (i : Fin size) : index size i.val = .ok i := by
  simp [index, i.isLt, pure, Except.pure]

@[simp] theorem slotAt_index (stack : Stack) (i : Fin stack.length) :
    slotAt stack i.val = .ok stack[i] := by simp [slotAt, index_eq]

theorem State.isFinal_iff (state : State source target spills) (i : Fin state.stack.length) :
    state.isFinal i ↔ ∃ h : i.val < state.stack.length, state.isFinal ⟨i.val, h⟩ :=
  ⟨fun hf => ⟨i.isLt, hf⟩, fun ⟨_, hf⟩ => hf⟩

-- Finality of an offset, read from the target side of the mapping.
theorem State.exists_isFinal_iff (state : State source target spills) (offset : ℕ) :
    (∃ h : offset < state.stack.length, state.isFinal ⟨offset, h⟩) ↔
      if h : offset < target.length then (state.mapping.symm ⟨offset, h⟩).map Fin.val = some offset
      else False := by
  constructor
  · rintro ⟨hs, hf⟩
    obtain ⟨d, hd, hval⟩ := Option.map_eq_some_iff.mp hf
    change d.val = offset at hval
    have hlt : offset < target.length := hval ▸ d.isLt
    simp only [hlt, ↓reduceDIte, Option.map_eq_some_iff]
    refine ⟨⟨offset, hs⟩, ?_, rfl⟩
    rw [PEquiv.eq_some_iff]
    exact hd.trans (congrArg some (Fin.ext hval))
  · intro h
    split_ifs at h with hlt
    obtain ⟨j, hj, hval⟩ := Option.map_eq_some_iff.mp h
    subst hval
    exact ⟨j.isLt, Option.map_eq_some_iff.mpr ⟨_, (PEquiv.eq_some_iff _).mp hj, rfl⟩⟩

theorem swapDestinations_result (state : State source target spills)
    (a b : Fin state.stack.length) :
    state.swapDestinations a.val b.val =
      .ok { state with mapping := state.mapping.swapDestinations a b } := by
  simp only [State.swapDestinations, index_eq]
  rfl

end Shuffler.Emission
