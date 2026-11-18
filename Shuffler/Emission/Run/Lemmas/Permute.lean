module

public import Shuffler.Emission.Run.Lemmas.Mapping
public import Shuffler.Permute.Execution

@[expose] public section

namespace Shuffler.Permute

open Emission

theorem go_frame (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) :
    ∀ {result}, permute.go state p hne = .ok result →
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue := by
  refine permute.go.induct_unfolding hne
    (motive := fun state _ run => state.stack.length = n → ∀ {result}, run = .ok result →
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue)
    ?top ?pos ?done state p hlen
  case top =>
    intro state p top ht perm' ih hlen result hr
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind] at hr
    by_cases he : state.stack[p top] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      obtain ⟨hp, hg, hb⟩ := ih { state with mapping := state.mapping.swapDestinations (p top) top } rfl hr
      exact ⟨hp, hg, hb.trans (boundValue_retag state (p top) top he)⟩
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable (p top)
    · have hvalid : state.stack.isValidSwapTarget (p top) :=
        ⟨by have := (p top).isLt; have := Fin.val_ne_of_ne ht; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal (p top)
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      obtain ⟨hp, hg, hb⟩ := ih _ (by simp) hr
      exact ⟨hp, hg, hb.trans (boundValue_swap state (p top) (state.stack.topOffset hne) _)⟩
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state (p top) hreach] at hr
      cases hr
      exact ⟨rfl, rfl, rfl⟩
  case pos =>
    intro state p top ht search pos hpos hsearch perm' ih hlen result hr
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind] at hr
    by_cases he : state.stack[pos] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      obtain ⟨hp, hg, hb⟩ := ih { state with mapping := state.mapping.swapDestinations pos top } rfl hr
      exact ⟨hp, hg, hb.trans (boundValue_retag state pos top he)⟩
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable pos
    · have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
      have hvalid : state.stack.isValidSwapTarget pos :=
        ⟨by have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal pos
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      obtain ⟨hp, hg, hb⟩ := ih _ (by simp) hr
      exact ⟨hp, hg, hb.trans (boundValue_swap state pos (state.stack.topOffset hne) _)⟩
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state pos hreach] at hr
      cases hr
      exact ⟨rfl, rfl, rfl⟩
  case done =>
    intro state _ _ _ _ _ _ result hr
    cases hr
    exact ⟨rfl, rfl, rfl⟩

theorem go_not_error_blocked (state : State source target spills) {n : ℕ} (p : Permutation n) (hne : n > 0)
    (hlen : state.stack.length = n) (b : Blocked) : permute.go state p hne ≠ .error (.Blocked b) := by
  refine permute.go.induct_unfolding hne
    (motive := fun state _ run => state.stack.length = n → ∀ b, run = .error (.Blocked b) → False)
    ?top ?pos ?done state p hlen b
  case top =>
    intro state p top ht perm' ih hlen b hr
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind] at hr
    by_cases he : state.stack[p top] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      exact ih { state with mapping := state.mapping.swapDestinations (p top) top } rfl b hr
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable (p top)
    · have hvalid : state.stack.isValidSwapTarget (p top) :=
        ⟨by have := (p top).isLt; have := Fin.val_ne_of_ne ht; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal (p top)
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      exact ih _ (by simp) b hr
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state (p top) hreach] at hr
      cases hr
  case pos =>
    intro state p top ht search pos hpos hsearch perm' ih hlen b hr
    subst hlen
    have htop : top.val = state.stack.length - 1 := rfl
    simp only [slotAt_index, except_ok_bind] at hr
    by_cases he : state.stack[pos] = state.stack[top]
    · simp only [he, ↓reduceIte, swapDestinations_result, except_ok_bind] at hr
      exact ih { state with mapping := state.mapping.swapDestinations pos top } rfl b hr
    simp only [he, ↓reduceIte, index_eq, except_ok_bind] at hr
    by_cases hreach : state.isSwapReachable pos
    · have hpos_ne : pos ≠ top := fun h => hpos (by rw [h]; exact not_not.mp ht)
      have hvalid : state.stack.isValidSwapTarget pos :=
        ⟨by have := pos.isLt; have := Fin.val_ne_of_ne hpos_ne; dsimp only; omega, hreach⟩
      simp only [hreach, not_true_eq_false, ↓reduceIte] at hr
      by_cases hfinal : state.isFinal pos
      · obtain ⟨_, hf⟩ := swapWith_final state _ hfinal
        rw [hf, except_error_bind] at hr
        cases hr
      rw [swapWith_result state _ hfinal hvalid, except_ok_bind] at hr
      exact ih _ (by simp) b hr
    · simp only [hreach, not_false_eq_true, ↓reduceIte, blockSwapUnreachable_eq state pos hreach] at hr
      cases hr
  case done =>
    intro state _ _ _ _ _ _ b hr
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
