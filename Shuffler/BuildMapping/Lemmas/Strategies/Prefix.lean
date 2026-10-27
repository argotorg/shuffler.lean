import Shuffler.BuildMapping.Lemmas.Strategies.Phases

namespace Shuffler.BuildMapping.Strategies

open MappingBuilder

-- The first two passes keep the dropped entries and leave the flag false.
theorem prefix_succeeds (source target : Stack) (dropped : List Byte)
    (hsizes : dropped.length = source.length) :
    Succeeds (initialPasses source target dropped) fun mb =>
      mb.dropped = dropped ∧ mb.sawWildcardCopy = false := by
  unfold initialPasses
  dsimp only
  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    Diagonal mb.mapping ∧ mb.dropped = dropped ∧ mb.sawWildcardCopy = false)
    _ _ _ ⟨diagonal_bot, rfl, rfl⟩ ?_).bind fun mb ⟨_, hd, hf⟩ => ?_
  · intro j mb ⟨hdiag, hd, hf⟩
    have hsize : mb.dropped.length = source.length := hd ▸ hsizes
    simp only [mappable_ok mb _ hsize, except_ok_bind]
    split
    · next hcond =>
      have hs : mb.IsMappable (Fin.castLE (min_le_left _ _) j) :=
        of_decide_eq_true hcond.2
      have ht := diagonal_symm_eq_none mb.mapping hdiag
        (Fin.castLE (min_le_left _ _) j) (Fin.castLE (min_le_right _ _) j) rfl hs.2
      rw [map_ok mb _ _ hs ht]
      exact ⟨diagonal_bind _ hdiag _ _ rfl hs.2 ht, hd, hf⟩
    · exact ⟨hdiag, hd, hf⟩
  refine (Succeeds.forIn (fun mb : MappingBuilder source target =>
    mb.dropped = dropped ∧ mb.sawWildcardCopy = false) _ _ _ ⟨hd, hf⟩ ?_).bind
    fun _ h => h
  intro t mb ⟨hd, hf⟩
  have hsize : mb.dropped.length = source.length := hd ▸ hsizes
  split
  · exact ⟨hd, hf⟩
  · next hfree =>
    refine (closestCopy_succeeds mb t _ hsize).bind fun r hr => ?_
    split
    · next copy =>
      rw [map_ok mb _ _ (hr copy rfl)
        (symm_eq_none_of_not_hasSourceAssigned mb t (not_or.mp hfree).1)]
      exact ⟨hd, hf⟩
    · exact ⟨hd, hf⟩

-- The phase definitions give the same computation as buildMapping.
theorem buildMapping_eq_phases (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) :
    buildMapping source target dropped strategy = (do
      _ ← requires (dropped.length = source.length) "dropped needs one entry per source slot"
      let mb ← initialPasses source target dropped
      let mb ← copyPass strategy mb
      let mb ← suffix mb
      pure { mapping := mb.mapping, sawWildcardCopy := mb.sawWildcardCopy }) := by
  simp only [buildMapping, initialPasses, copyPass, suffix, bind_assoc, pure_bind]
  rfl

end Shuffler.BuildMapping.Strategies
