import Shuffler.BuildBottomUp.Lemmas.StaticInvariant
import Shuffler.BuildBottomUp.Lemmas.StaticCompletion
import Shuffler.BuildBottomUp.Lemmas.StaticGeneration

namespace Shuffler.BuildBottomUp.Success

theorem appended_valid (state : State source target spills) (h : state.Valid)
    (d : Fin target.length) (hd : state.mapping.symm d = none) (v : Value)
    (trace : Trace spills source (state.stack ++ [v])) : (appended state d hd v trace).Valid := by
  have hpositive : 0 < state.pending_generations := by
    rw [← h.pending]
    apply Finset.card_pos.mpr
    exact ⟨d, by simp [hd]⟩
  have hcount := Mapping.unmapped_target_slots_push state.mapping d hd
  refine ⟨?_, ?_, ?_⟩
  · change (state.stack ++ [v]).length + (state.pending_generations - 1) = target.length
    simp only [List.length_append, List.length_singleton]
    have := h.size
    omega
  · simp only [appended, Mapping.unmapped_target_slots_cast]
    have := h.pending
    omega
  · intro j
    exact state.isAvailable_of_subset (appended state d hd v trace)
      (List.subset_append_left _ _) j (h.available j)

theorem completedPermutation_produced {state produced : State source target spills}
    (hstate : state.Valid) (hproduced : produced.Valid) (dest : Fin target.length)
    (hb : state.mapping.symm dest = none)
    (hg : Growth state produced dest (state.pending_generations - 1))
    (hm : ProducedMapping state produced dest)
    (hmin : ∀ j, state.mapping.symm j = none → dest ≤ j) :
    completedPermutation produced hproduced = completedPermutation state hstate := by
  let trace : Trace spills source (state.stack ++ [target[dest]]) := hg.stack_eq ▸ produced.trace
  let app := appended state dest hb target[dest] trace
  have happ : app.Valid := appended_valid state hstate dest hb target[dest] trace
  have hmap : ProducedMapping state app dest := producedMapping_append state target[dest] dest hb trace _
  calc
    completedPermutation produced hproduced = completedPermutation app happ := by
      apply completedPermutation_congr produced app hproduced happ (congrArg List.length hg.stack_eq)
      intro j
      exact (hm j).trans (hmap j).symm
    _ = completedPermutation state hstate :=
      completedPermutation_appended state hstate dest hb target[dest] trace happ hmin

theorem PrefixState.produced_retag {initial state produced : State source target spills}
    {h : initial.Valid} (hp : PrefixState initial h cursor state) (hc : cursor < target.length)
    (hb : state.mapping.symm ⟨cursor,hc⟩ = none)
    (hg : Growth state produced ⟨cursor,hc⟩ (state.pending_generations - 1))
    (hm : ProducedMapping state produced ⟨cursor,hc⟩)
    (current top : Fin produced.stack.length) (hcurrent : current.val = cursor)
    (hbprod : produced.mapping.symm ⟨cursor,hc⟩ = some top)
    (hv : produced.stack[current] = produced.stack[top]) :
    PrefixState initial h (cursor+1) (retagged produced current top) := by
  have hiprod := hg.generation.invariant hp.invariant
  have hge := hiprod.processed.bound_ge ⟨cursor,hc⟩ top hbprod le_rfl
  have hfinal : ∃ h, (retagged produced current top).isFinal ⟨cursor, h⟩ := by
    have hmap : (retagged produced current top).mapping.symm ⟨cursor,hc⟩ = some current := by
      simp [retagged, hbprod]
    exact ((retagged produced current top).isFinal_of_bound_iff _ _ hmap).mpr hcurrent
  have hi := (hiprod.retag current top (by omega) hge).advance hfinal
  have hhole : initial.mapping.symm ⟨cursor,hc⟩ = none := (hp.unbound _).mp hb |>.1
  have hmin : ∀ j, state.mapping.symm j = none → (⟨cursor,hc⟩ : Fin target.length) ≤ j := by
    intro j hj
    exact ((hp.unbound j).mp hj).2
  have hcomplete : completedPermutation produced hiprod.valid =
      completedPermutation state hp.invariant.valid :=
    completedPermutation_produced hp.invariant.valid hiprod.valid ⟨cursor,hc⟩ hb hg hm hmin
  refine ⟨hi, ?_, ?_, ?_, ?_⟩
  · change produced.stack = _
    rw [hg.stack_eq, hp.stack_eq, augmentedStack_take_succ_hole initial cursor hc hhole]
    simp only [Fin.getElem_fin]
  · intro j
    simp only [retagged, Mapping.swapDestinations_symm_apply, Option.map_eq_none_iff,
      hg.unbound, hp.unbound]
    constructor
    · rintro ⟨hne, hj, hge⟩
      refine ⟨hj, ?_⟩
      have hnval : j.val ≠ cursor := by
        intro he
        apply hne
        exact Fin.ext he
      omega
    · rintro ⟨hj, hge⟩
      refine ⟨?_, hj, by omega⟩
      intro he
      have := congrArg Fin.val he
      change j.val = cursor at this
      omega
  · exact (expectedStack_retag produced current top hv).symm.trans (hg.expected.trans hp.expected)
  · rw [completedPermutation_retagged]
    have hcur : stackIndex produced hiprod.valid current = ⟨cursor,hc⟩ := Fin.ext hcurrent
    have hbound : completedPermutation produced hiprod.valid (stackIndex produced hiprod.valid top) =
        ⟨cursor,hc⟩ := by
      apply Fin.ext
      rw [completedPermutation_val]
      simp [completedNext, stackIndex, top.isLt, produced.mapping.eq_some_iff.mp hbprod]
    rw [hcomplete] at hbound
    rw [hcur, hcomplete]
    exact hp.cycles.step_of_apply hc (stackIndex produced hiprod.valid top) hbound

end Shuffler.BuildBottomUp.Success
