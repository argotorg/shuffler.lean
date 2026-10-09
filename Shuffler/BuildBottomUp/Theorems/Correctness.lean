import Shuffler.BuildBottomUp.Lemmas.LoopProofs

namespace Shuffler.BuildBottomUp

-- On success, each bound target slot holds the value of its bound stack slot, and each unbound
-- target slot holds its target value.
theorem buildBottomUp_expected_of_ok (initial : State source target spills)
    (h : initial.Valid) {res : Stack} {trace : Trace spills source res}
    (hrun : buildBottomUp initial h = .ok ⟨res, trace⟩) :
    res = initial.expectedStack := by
  have hs := buildBottomUp_spec initial h
  simpa [hrun, Spec] using hs

-- If the mapping connects only slots of equal value, a successful run returns the target.
theorem buildBottomUp_correct_of_ok (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j])
    {res : Stack} {trace : Trace spills source res}
    (hrun : buildBottomUp initial h = .ok ⟨res, trace⟩) : res = target :=
  (buildBottomUp_expected_of_ok initial h hrun).trans (expectedStack_eq_target initial hmapped)

end Shuffler.BuildBottomUp
