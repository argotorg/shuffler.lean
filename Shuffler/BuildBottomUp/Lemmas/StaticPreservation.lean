import Shuffler.BuildBottomUp.Lemmas.StaticInvariant
import Shuffler.BuildBottomUp.Lemmas.StaticCompletion
import Shuffler.BuildBottomUp.Lemmas.StaticGeneration

namespace Shuffler.BuildBottomUp.Success

theorem completedPermutation_of_bound (state : State source target spills) (h : state.Valid)
    (carrier : Fin state.stack.length) (dest : Fin target.length)
    (hb : state.mapping.symm dest = some carrier) :
    completedPermutation state h (stackIndex state h carrier) = dest := by
  apply Fin.ext
  rw [completedPermutation_val]
  simp [completedNext, stackIndex, carrier.isLt, state.mapping.eq_some_iff.mp hb]

theorem PrefixState.retag {initial state : State source target spills} {h : initial.Valid}
    (hp : PrefixState initial h cursor state) (hc : cursor < target.length)
    (current carrier : Fin state.stack.length) (hcurrent : current.val = cursor)
    (hb : state.mapping.symm ⟨cursor, hc⟩ = some carrier)
    (hv : state.stack[current] = state.stack[carrier]) :
    PrefixState initial h (cursor + 1) (retagged state current carrier) := by
  have hge := hp.invariant.processed.bound_ge ⟨cursor, hc⟩ carrier hb le_rfl
  have hfinal : ∃ h, (retagged state current carrier).isFinal ⟨cursor, h⟩ := by
    have hmap : (retagged state current carrier).mapping.symm ⟨cursor, hc⟩ = some current := by
      simp [retagged, hb]
    exact ((retagged state current carrier).isFinal_of_bound_iff _ _ hmap).mpr hcurrent
  have hi := (hp.invariant.retag current carrier (by omega) hge).advance hfinal
  have hb0 : (initial.mapping.symm ⟨cursor, hc⟩).isSome := by
    cases he : initial.mapping.symm ⟨cursor, hc⟩ with
    | some pos => rfl
    | none =>
      have hn := (hp.unbound ⟨cursor, hc⟩).mpr ⟨he, le_rfl⟩
      simp [hb] at hn
  refine ⟨hi, ?_, ?_, ?_, ?_⟩
  · change state.stack = _
    rw [prefixLength, generatedBefore_succ_of_bound initial cursor hc hb0]
    exact hp.stack_eq
  · intro j
    simp only [retagged, Mapping.swapDestinations_symm_apply, Option.map_eq_none_iff, hp.unbound]
    constructor
    · rintro ⟨hj, hjc⟩
      refine ⟨hj, ?_⟩
      by_contra hn
      have he : j = ⟨cursor, hc⟩ := Fin.ext (show j.val = cursor by omega)
      subst j
      simp [hj] at hb0
    · rintro ⟨hj, hjc⟩
      exact ⟨hj, by omega⟩
  · exact (expectedStack_retag state current carrier hv).symm.trans hp.expected
  · rw [completedPermutation_retagged]
    have he : stackIndex state hp.invariant.valid current = ⟨cursor, hc⟩ := Fin.ext hcurrent
    rw [he]
    exact hp.cycles.step_of_apply hc (stackIndex state hp.invariant.valid carrier)
      (completedPermutation_of_bound state hp.invariant.valid carrier _ hb)

end Shuffler.BuildBottomUp.Success
