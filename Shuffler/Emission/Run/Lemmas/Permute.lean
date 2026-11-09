module

public import Shuffler.Emission.Run.Lemmas.Mapping
public import Shuffler.Permute.Execution

@[expose] public section

namespace Shuffler.Permute

open Emission

theorem go_frame (state : State source target spills) (p : Permutation state.stack)
    (hne : 0 < state.stack.length) :
    ∀ {result}, permute.go state p hne = .ok result →
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue := by
  refine permute.go.induct_unfolding
    (motive := fun state _ _ run => ∀ {result}, run = .ok result →
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue)
    ?equal_top ?blocked_top ?assert_top ?swap_top ?equal_pos ?blocked_pos ?assert_pos ?swap_pos ?done
    state p hne
    <;> intro state p hne top htop <;> intros
  case assert_top result hr | assert_pos result hr => cases hr
  case equal_top ht perm' he ih result hr =>
    obtain ⟨hp, hg, hb⟩ := ih hr
    exact ⟨hp, hg, hb.trans (boundValue_retag state (p top) top he)⟩
  case equal_pos ht search pos hpos hsearch perm' he ih result hr =>
    obtain ⟨hp, hg, hb⟩ := ih hr
    exact ⟨hp, hg, hb.trans (boundValue_retag state pos top he)⟩
  case swap_top ht perm' he idx hdepth hfinal stack' h1 h2 h3 trace' ih result hr =>
    obtain ⟨hp, hg, hb⟩ := ih hr
    refine ⟨hp, hg, hb.trans ?_⟩
    have hi : state.stack.length - 1 - idx = (p top).val := by dsimp [idx, Fin.rev]; omega
    have htoplt : state.stack.length - 1 < state.stack.length := by omega
    funext dest
    simp only [State.boundValue, Mapping.positionOf, Mapping.cast_symm,
      Mapping.swapDestinations_symm_apply, Option.map_map]
    cases state.mapping.symm dest with
    | none => rfl
    | some i =>
      by_cases ha : i = (p top)
      · subst i; simp [Function.comp_apply, stack', hi, htop]
      by_cases hb : i = top
      · subst i; simp [Function.comp_apply, stack', hi, htop, htoplt]
      have hib : i.val ≠ state.stack.length - 1 := by simpa only [htop] using Fin.val_ne_of_ne hb
      simp [Function.comp_apply, stack', Equiv.swap_apply_of_ne_of_ne ha hb,
        hi, Fin.val_ne_of_ne ha, hib]
  case swap_pos ht search pos hpos hsearch perm' he idx hdepth hfinal hpos_ne hlt stack' h1 h2 h3 trace'
      ih result hr =>
    obtain ⟨hp, hg, hb⟩ := ih hr
    refine ⟨hp, hg, hb.trans ?_⟩
    have hi : state.stack.length - 1 - idx = pos.val := by dsimp [idx, Fin.rev]; omega
    have htoplt : state.stack.length - 1 < state.stack.length := by omega
    funext dest
    simp only [State.boundValue, Mapping.positionOf, Mapping.cast_symm,
      Mapping.swapDestinations_symm_apply, Option.map_map]
    cases state.mapping.symm dest with
    | none => rfl
    | some i =>
      by_cases ha : i = pos
      · subst i; simp [Function.comp_apply, stack', hi, htop]
      by_cases hb : i = top
      · subst i; simp [Function.comp_apply, stack', hi, htop, htoplt]
      have hib : i.val ≠ state.stack.length - 1 := by simpa only [htop] using Fin.val_ne_of_ne hb
      simp [Function.comp_apply, stack', Equiv.swap_apply_of_ne_of_ne ha hb,
        hi, Fin.val_ne_of_ne ha, hib]
  case blocked_top ht he idx hdepth result hr =>
    rw [blockSwapUnreachable_eq state (p top)
      (by rw [State.isSwapReachable, Stack.isSwapReachable, ← State.depthOf, depthOf_eq_rev, not_le]; exact hdepth)] at hr
    cases hr
    exact ⟨rfl, rfl, rfl⟩
  case blocked_pos ht search pos hpos hsearch he idx hdepth result hr =>
    rw [blockSwapUnreachable_eq state pos
      (by rw [State.isSwapReachable, Stack.isSwapReachable, ← State.depthOf, depthOf_eq_rev, not_le]; exact hdepth)] at hr
    cases hr
    exact ⟨rfl, rfl, rfl⟩
  case done ht search hsearch result hr =>
    cases hr
    exact ⟨rfl, rfl, rfl⟩

theorem go_not_error_blocked (state : State source target spills) (p : Permutation state.stack)
    (hne : 0 < state.stack.length) (b : Blocked) : permute.go state p hne ≠ .error (.Blocked b) := by
  refine permute.go.induct_unfolding
    (motive := fun _ _ _ run => ∀ b, run = .error (.Blocked b) → False)
    ?equal_top ?blocked_top ?assert_top ?swap_top ?equal_pos ?blocked_pos ?assert_pos ?swap_pos ?done
    state p hne b
    <;> intro state p hne top htop <;> intros
  case equal_top ht perm' he ih b hr => exact ih b hr
  case equal_pos ht search pos hpos hsearch perm' he ih b hr => exact ih b hr
  case swap_top ht perm' he idx hdepth hfinal stack' h1 h2 h3 trace' ih b hr => exact ih b hr
  case swap_pos ht search pos hpos hsearch perm' he idx hdepth hfinal hpos_ne hlt stack' h1 h2 h3 trace'
      ih b hr => exact ih b hr
  case assert_top b hr | assert_pos b hr | done b hr => cases hr
  case blocked_top ht he idx hdepth b hr =>
    rw [blockSwapUnreachable_eq state (p top)
      (by rw [State.isSwapReachable, Stack.isSwapReachable, ← State.depthOf, depthOf_eq_rev, not_le]; exact hdepth)] at hr
    cases hr
  case blocked_pos ht search pos hpos hsearch he idx hdepth b hr =>
    rw [blockSwapUnreachable_eq state pos
      (by rw [State.isSwapReachable, Stack.isSwapReachable, ← State.depthOf, depthOf_eq_rev, not_le]; exact hdepth)] at hr
    cases hr

theorem permute_result_spec (state : State source target spills) (p : Permutation state.stack)
    (hagree : bindings_agree state p) :
    ∃ result, permute state p = .ok result ∧
      result.state.stack.length = state.stack.length ∧
      result.state.planned_mapping = state.planned_mapping ∧
      result.state.pending_generations = state.pending_generations ∧
      result.state.boundValue = state.boundValue ∧
      ∀ b, result.blocked = some b → 0 < b.excess := by
  obtain ⟨q, hq, hinv⟩ := normalize_goInv state p hagree
  rw [permute_eq_normalize, hq, except_ok_bind]
  by_cases hne : 0 < state.stack.length
  · rw [dite_eq_left hne]
    obtain ⟨result, hr⟩ := go_ok state q hne _ hinv
    have hs := go_spec state q hne result hr
    obtain ⟨hp, hg, hb⟩ := go_frame state q hne hr
    exact ⟨result, hr, hs.length, hp, hg, hb, fun b h => (hs.blocked b h).choose_spec.2.1⟩
  · rw [dite_eq_right hne]
    exact ⟨⟨none, state⟩, rfl, rfl, rfl, rfl, rfl, by simp⟩

end Shuffler.Permute
