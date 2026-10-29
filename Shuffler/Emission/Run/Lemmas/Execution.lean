module

public import Shuffler.Emission.Run.Defs
public import Shuffler.PermuteAtLowestHeight.Lemmas
public import Shuffler.Emission.Run.Lemmas.RemoveSurplus
public import Shuffler.Emission.Run.Lemmas.BuildBottomUp
import Shuffler.BuildBottomUp.Theorems.Safety

@[expose] public section

namespace Shuffler.Emission

theorem run_spec (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet)
    (havailable : ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      spills.is_spilled target[j] ∨
      ∃ i dest, mapping i = some dest ∧ source[i] = target[j])
    (hlabels : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (mapping.symm j).isSome) :
    ∃ result, run source target mapping spills = .ok result ∧
      result.state.planned_mapping = mapping ∧ result.Positive := by
  let initial : State source target spills := {
    planned_mapping := mapping, stack := source, trace := .Lit source,
    mapping, pending_generations := mapping.unmapped_target_slots }
  obtain ⟨removed, hr⟩ := removeSurplus_ok initial
  obtain ⟨hrplan, hrpending, hrpositive⟩ := removeSurplus_frame initial hr
  unfold run
  change ∃ result, (removeSurplus initial >>= _) = .ok result ∧ _
  rw [hr, except_ok_bind]
  cases hblocked : removed.blocked with
  | some blocked =>
    simp only [Option.isSome_some, ↓reduceIte]
    exact ⟨removed, rfl, hrplan, hrpositive⟩
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hre : removeSurplus initial = .ok ⟨none, removed.state⟩ := by
      simpa only [← hblocked] using hr
    have htotal : ∀ i, (removed.state.mapping.destinationOf i).isSome := by
      simpa only [State.noSurplus, State.isSurplus, Option.isSome_iff_ne_none] using
        removeSurplus_noSurplus initial removed.state hre
    have hrbound := removeSurplus_keeps_bindings initial removed.state hre
    have hrbound' : removed.state.boundValue = initial.boundValue := funext hrbound
    have hdom : ∀ j, (removed.state.mapping.symm j).isSome =
        (removed.state.planned_mapping.symm j).isSome := by
      intro j
      rw [← boundValue_isSome, hrbound', boundValue_isSome, hrplan]
    obtain ⟨permuted, hp, hlength, hpplan, hppending, hpbound, hppositive⟩ :=
      Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight_result_spec removed.state htotal hdom
    rw [hp, except_ok_bind]
    cases hpblocked : permuted.blocked with
    | some blocked =>
      simp only [Option.isSome_some, ↓reduceIte]
      exact ⟨permuted, rfl, hpplan.trans hrplan, hppositive⟩
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have hbound : permuted.state.boundValue = initial.boundValue := hpbound.trans hrbound'
      have hsize : permuted.state.stack.length + permuted.state.pending_generations = target.length := by
        rw [hlength, hppending, hrpending]
        have hcount := unmapped_of_boundValue_eq initial removed.state hrbound'
        simpa only [initial, ← hcount] using Mapping.total_size removed.state.mapping htotal
      have hpending : permuted.state.mapping.unmapped_target_slots = permuted.state.pending_generations := by
        rw [unmapped_of_boundValue_eq initial permuted.state hbound, hppending, hrpending]
      have havailable : ∀ i, permuted.state.isAvailable i := by
        apply available_of_boundValue
        intro j
        rcases havailable j with h | h | ⟨i, dest, hb, hv⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ⟨dest, ?_⟩)
          rw [hbound]
          simp only [State.boundValue, initial, Mapping.positionOf,
            mapping.eq_some_iff.mpr hb, Option.map_some]
          exact congrArg some hv
      have hlabels' : ∀ j : Fin target.length,
          target[j].isFunctionReturnLabel → (permuted.state.mapping.symm j).isSome := by
        intro j hj
        rw [← boundValue_isSome, hbound, boundValue_isSome]
        exact hlabels j hj
      rw [requires_of_true _ hsize, except_ok_bind,
        requires_of_true _ hpending, except_ok_bind, requires_of_true _ havailable, except_ok_bind,
        requires_of_true _ (by simpa only [Fin.getElem_fin] using hlabels'), except_ok_bind]
      obtain ⟨result, hb, hbpositive, hbplan⟩ :=
        buildBottomUp_ok permuted.state ⟨hsize, hpending, havailable, hlabels'⟩
      exact ⟨result, hb, hbplan.trans (hpplan.trans hrplan), hbpositive⟩

end Shuffler.Emission
