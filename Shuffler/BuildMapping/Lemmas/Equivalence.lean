import Shuffler.BuildMapping.Defs

namespace Shuffler.BuildMapping.Equivalence

theorem buildMapping_eq (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) :
    buildMapping_new source target dropped strategy = buildMapping source target dropped strategy := by
  simp only [buildMapping_new, buildMapping, ← not_or, ite_not]
  congr 1
  funext _
  congr 1
  funext mb
  congr 1
  congr 1
  funext j mb
  -- Compare the second loop for both guard outcomes and both search results.
  by_cases h : mb.hasSourceAssigned j ∨ mb.isWildcardTarget j
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    congr 1
    funext copy
    cases copy <;> rfl

end Shuffler.BuildMapping.Equivalence
