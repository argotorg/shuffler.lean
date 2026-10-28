import Shuffler.BuildMapping.Lemmas.Strategies.Phases

namespace Shuffler.BuildMapping.Strategies

variable {source target : Stack}

open MappingBuilder

-- Binding a wildcard target keeps the inverse lookup at every other target.
private theorem bind_symm_non_wildcard (mapping : Mapping source.length target.length)
    (s : Fin source.length) (t : Fin target.length)
    (hs : mapping s = none) (ht : mapping.symm t = none) (hwild : target[t].is_junk)
    (u : Fin target.length) (hu : ¬ target[u].is_junk) :
    (mapping.bind s t hs ht).symm u = mapping.symm u := by
  apply Mapping.bind_symm_apply_of_ne
  intro heq
  subst u
  exact hu hwild

-- The last two passes bind only wildcard targets and do not change the copy flag.
theorem suffix_succeeds (mb : MappingBuilder source target)
    (hsize : mb.dropped.length = source.length) :
    Succeeds (suffix mb) fun result =>
      result.dropped.length = source.length ∧
      result.sawWildcardCopy = mb.sawWildcardCopy ∧
      ∀ t, ¬ target[t].is_junk → result.mapping.symm t = mb.mapping.symm t := by
  unfold suffix
  refine (Succeeds.forIn (fun current : MappingBuilder source target =>
    current.dropped.length = source.length ∧
    current.sawWildcardCopy = mb.sawWildcardCopy ∧
    ∀ t, ¬ target[t].is_junk → current.mapping.symm t = mb.mapping.symm t)
    _ _ _ ⟨hsize, rfl, fun _ _ => rfl⟩ ?_).bind fun current hinv => ?_
  · intro j current ⟨hsize, hflag, hlookup⟩
    unfold keepStep
    simp only [mappable_ok current _ hsize, except_ok_bind]
    split
    · next hcond =>
      have hs := of_decide_eq_true hcond.2.2
      have ht := symm_eq_none_of_not_hasSourceAssigned current _ hcond.2.1
      have hwild := of_decide_eq_true hcond.1
      rw [map_ok current _ _ hs ht]
      refine ⟨hsize, hflag, ?_⟩
      intro u hu
      exact (bind_symm_non_wildcard current.mapping _ _ hs.2 ht hwild u hu).trans (hlookup u hu)
    · exact ⟨hsize, hflag, hlookup⟩
  refine Succeeds.forIn (fun current : MappingBuilder source target =>
    current.dropped.length = source.length ∧
    current.sawWildcardCopy = mb.sawWildcardCopy ∧
    ∀ t, ¬ target[t].is_junk → current.mapping.symm t = mb.mapping.symm t)
    _ _ _ hinv ?_
  intro t current ⟨hsize, hflag, hlookup⟩
  unfold surplusStep
  dsimp only
  split
  · exact ⟨hsize, hflag, hlookup⟩
  · next hfree =>
    refine (closestSurplus_succeeds current t hsize).bind fun r hr => ?_
    split
    · next best =>
      have hs := hr best rfl
      have ht := symm_eq_none_of_not_hasSourceAssigned current t (not_or.mp hfree).1
      have hwild := of_decide_eq_true (Decidable.of_not_not (not_or.mp hfree).2)
      rw [map_ok current _ _ hs ht]
      refine ⟨hsize, hflag, ?_⟩
      intro u hu
      exact (bind_symm_non_wildcard current.mapping _ _ hs.2 ht hwild u hu).trans (hlookup u hu)
    · exact ⟨hsize, hflag, hlookup⟩

end Shuffler.BuildMapping.Strategies
