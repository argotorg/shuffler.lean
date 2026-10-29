module

public import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildBottomUp.Lemmas.LoopProofs
import Shuffler.BuildBottomUp.Lemmas.Values

@[expose] public section

namespace Shuffler.Emission

-- On success, each bound target slot holds the value of its bound stack slot, and each unbound
-- target slot holds its target value.
theorem buildBottomUp_expected_of_ok (initial : State source target spills)
    (h : initial.Valid) {result : State source target spills}
    (hrun : buildBottomUp initial h = .ok ⟨none, result⟩) :
    result.stack = initial.expectedStack := by
  have hs := buildBottomUp_spec initial h
  simpa [completedTrace_of_ok hrun, Spec] using hs

-- If the mapping connects only slots of equal value, a successful run returns the target.
theorem buildBottomUp_correct_of_ok (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j])
    {result : State source target spills}
    (hrun : buildBottomUp initial h = .ok ⟨none, result⟩) : result.stack = target :=
  (buildBottomUp_expected_of_ok initial h hrun).trans (expectedStack_eq_target initial hmapped)

end Shuffler.Emission
