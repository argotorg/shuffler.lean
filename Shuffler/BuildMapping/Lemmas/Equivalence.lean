import Shuffler.BuildMapping.Defs

namespace Shuffler.BuildMapping.Equivalence

-- Setting the flag before `map` gives the same result, including errors, as setting it after.
private theorem map_set_sawWildcardCopy (mb : MappingBuilder source target)
    (s : Fin source.length) (t : Fin target.length) :
    ({ mb with sawWildcardCopy := true } : MappingBuilder source target).map s t =
      (do
        let next ← mb.map s t
        pure { next with sawWildcardCopy := true }) := by
  simp only [MappingBuilder.map, bind_assoc, pure_bind]
  rfl

private theorem surplus_search_eq (mb : MappingBuilder source target) (j : Fin target.length) :
    (do
      let mut best : Option (Fin source.length) := none
      for o in List.finRange source.length do
        if (← mb.mappable o) ∧
            (¬ best.isSome ∨ best.any (λ b => mb.absDiff o j < mb.absDiff b j)) then
          best := some o
      return best) = mb.closestSurplus j := by
  simp only [MappingBuilder.closestSurplus, bind_pure]
  congr 1
  funext o best
  congr 1
  funext mappable
  cases mappable <;> cases best <;> simp

theorem buildMapping_eq (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) :
    buildMapping_new source target dropped strategy = buildMapping source target dropped strategy := by
  simp only [buildMapping_new, buildMapping, ← not_or, ite_not,
    map_set_sawWildcardCopy, bind_assoc, pure_bind]
  congr 1
  funext _
  congr 1
  funext mb
  congr 1
  · -- Compare the second loop for both guard outcomes and both search results.
    congr 1
    funext j mb
    by_cases h : mb.hasSourceAssigned j ∨ mb.isWildcardTarget j
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      congr 1
      funext copy
      cases copy <;> rfl
  · -- Compare the third loop after moving the flag update past `map`.
    funext mb
    congr 1
    · congr 1
      funext j mb
      by_cases h : mb.hasSourceAssigned j ∨ mb.isWildcardTarget j
      · simp only [h, ite_true]
      · simp only [h, ite_false]
        congr 1
        funext copy
        cases copy <;> rfl
    · funext mb
      congr 1
      funext mb
      -- The fourth loop is definitionally equal; compare the final loop.
      congr 1
      congr 1
      funext j mb
      by_cases hwild : mb.isWildcardTarget j <;>
        by_cases hassigned : mb.hasSourceAssigned j <;>
          simp [hwild, hassigned]
      have hsearch := surplus_search_eq mb j
      simp at hsearch
      rw [hsearch]
      congr 1
      funext best
      cases best <;> simp

end Shuffler.BuildMapping.Equivalence
