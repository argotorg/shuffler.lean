module

public import Shuffler.RemoveSurplus.Theorems
public import Shuffler.BuildBottomUp.Defs
import Mathlib.Data.List.FinRange

@[expose] public section

namespace Mapping

theorem bound_card (mapping : Mapping n m) :
    (Finset.univ.filter fun i => (mapping i).isSome).card =
      (Finset.univ.filter fun j => (mapping.symm j).isSome).card := by
  apply Finset.card_bij (fun i hi => (mapping i).get (by simpa using hi))
  · intro i hi
    have hb := Option.some_get (show (mapping i).isSome from by simpa using hi)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mapping.eq_some_iff.mpr hb.symm]
    rfl
  · intro a ha b hb he
    have ha' := Option.some_get (show (mapping a).isSome from by simpa using ha)
    have hb' := Option.some_get (show (mapping b).isSome from by simpa using hb)
    have h := (mapping.eq_some_iff.mpr ha'.symm).symm.trans
      (he ▸ mapping.eq_some_iff.mpr hb'.symm)
    exact Option.some.inj h
  · intro j hj
    have hs : (mapping.symm j).isSome := by simpa using hj
    let i := (mapping.symm j).get hs
    have hi : mapping i = some j := mapping.eq_some_iff.mp (Option.some_get hs).symm
    refine ⟨i, by simp [hi], ?_⟩
    simp [hi]

theorem total_size (mapping : Mapping n m) (htotal : ∀ i, (mapping i).isSome) :
    n + mapping.unmapped_target_slots = m := by
  have hc := bound_card mapping
  have hp := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun j => (mapping.symm j).isSome)
  simp only [Mapping.unmapped_target_slots]
  simpa [htotal, Option.not_isSome, ← hc] using hp

end Mapping

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

theorem boundValue_isSome (state : State source target spills) (j : Fin target.length) :
    (state.boundValue j).isSome = (state.mapping.symm j).isSome := by
  simp [State.boundValue, Mapping.positionOf]

theorem unmapped_of_boundValue_eq (initial result : State source target spills)
    (hb : result.boundValue = initial.boundValue) :
    result.mapping.unmapped_target_slots = initial.mapping.unmapped_target_slots := by
  unfold Mapping.unmapped_target_slots
  congr 1
  ext j
  have h := congrArg (fun f => (f j).isSome) hb
  simp only [boundValue_isSome] at h
  cases hr : result.mapping.symm j <;> cases hi : initial.mapping.symm j <;>
    simp_all

theorem available_of_boundValue (state : State source target spills)
    (ha : ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      spills.is_spilled target[j] ∨ ∃ dest, state.boundValue dest = some target[j]) :
    ∀ j, state.isAvailable j := by
  intro j
  rcases ha j with h | h | ⟨dest, hd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨pos, _, hv⟩ := Option.map_eq_some_iff.mp hd
    exact Or.inr (Or.inr (by
      rw [Stack.shallowestCopyPosition]
      apply List.find?_isSome.mpr
      exact ⟨pos, List.mem_reverse.mpr (List.mem_finRange _), by simpa using hv⟩))

end Shuffler.Emission
