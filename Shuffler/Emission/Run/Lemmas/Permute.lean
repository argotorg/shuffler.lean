module

public import Shuffler.Emission.Run.Lemmas.Mapping
public import Shuffler.Permute.Execution

@[expose] public section

namespace Shuffler.Permute

open Emission

-- Exchanging two slots together with their destinations keeps every target's value.
theorem Exchanged.boundValue {state next : State source target spills} {top pos : Fin state.stack.length}
    (hx : Exchanged state next top pos) : next.boundValue = state.boundValue := by
  funext dest
  simp only [State.boundValue, Mapping.positionOf]
  cases hq : state.mapping.symm dest with
  | none =>
    cases hn : next.mapping.symm dest with
    | none => rfl
    | some i =>
      rw [PEquiv.eq_some_iff, hx.mapping i (Fin.cast hx.length i) rfl, ← PEquiv.eq_some_iff, hq] at hn
      cases hn
  | some q =>
    have hn : next.mapping.symm dest = some (Fin.cast hx.length.symm (Equiv.swap top pos q)) := by
      rw [PEquiv.eq_some_iff, hx.mapping _ (Equiv.swap top pos q) rfl, Equiv.swap_apply_self,
        ← PEquiv.eq_some_iff, hq]
    have hs := hx.stack (Equiv.swap top pos q)
    simp only [Equiv.swap_apply_self] at hs
    rw [hn, Option.map_some, Option.map_some]
    exact (List.getElem?_eq_getElem _).symm.trans hs

theorem go_frame (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) :
    ∀ {result}, permute.go state p hne = .ok result →
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue := by
  refine go_induct hne (motive := fun state _ run => state.stack.length = n → ∀ {result}, run = .ok result →
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue)
    ?_ ?_ state p hlen
  · intro top htop state p pos hpos _ _ ih hlen result hr
    subst hlen
    rcases exchangeWithTop_cases state top pos htop hpos with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨next, hx, he⟩
    · simp only [he, except_ok_bind, Option.isSome_some, ↓reduceIte] at hr
      cases hr
      exact ⟨rfl, rfl, rfl⟩
    · rw [he, except_error_bind] at hr
      cases hr
    · simp only [he, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
      obtain ⟨hp, hg, hb⟩ := ih ⟨none, next⟩ hx.length hr
      exact ⟨hp.trans hx.planned, hg.trans hx.pending, hb.trans hx.boundValue⟩
  · intro state _ result hr
    cases hr
    exact ⟨rfl, rfl, rfl⟩

theorem go_not_error_blocked (state : State source target spills) {n : ℕ} (p : Permutation n)
    (hne : n > 0) (hlen : state.stack.length = n) (b : Blocked) :
    permute.go state p hne ≠ .error (.Blocked b) := by
  refine go_induct hne (motive := fun state _ run =>
      state.stack.length = n → ∀ b, run = .error (.Blocked b) → False)
    ?_ ?_ state p hlen b
  · intro top htop state p pos hpos _ _ ih hlen b hr
    subst hlen
    rcases exchangeWithTop_cases state top pos htop hpos with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨next, hx, he⟩
    · simp only [he, except_ok_bind, Option.isSome_some, ↓reduceIte] at hr
      cases hr
    · rw [he, except_error_bind] at hr
      cases hr
    · simp only [he, except_ok_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr
      exact ih ⟨none, next⟩ hx.length b hr
  · intro state _ b hr
    cases hr

theorem permute_result_spec (state : State source target spills) (p : Permutation state.stack.length)
    (hagree : bindings_agree state p) :
    ∃ result, permute state p = .ok result ∧
      result.state.stack.length = state.stack.length ∧
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue ∧
      ∀ b, result.blocked = some b → 0 < b.excess := by
  have hinv := normalize_goInv state p hagree
  dsimp only [permute]
  rw [← Permute.normalize]
  generalize normalize state.stack p = q at *
  by_cases hne : 0 < state.stack.length
  · rw [dite_eq_left hne]
    obtain ⟨result, hr⟩ := go_ok state q hne rfl _ hinv
    have hs := go_spec state q hne rfl result hr
    obtain ⟨hp, hg, hb⟩ := go_frame state q hne rfl hr
    exact ⟨result, hr, hs.length, hp, hg, hb, fun b h => (hs.blocked b h).choose_spec.2.1⟩
  · rw [dite_eq_right hne]
    exact ⟨⟨none, state⟩, rfl, rfl, rfl, rfl, rfl, by simp⟩

end Shuffler.Permute
