import Shuffler.BuildBottomUp.Theorems.Correctness
import Shuffler.BuildBottomUp.Lemmas.StaticProof
import Shuffler.BuildBottomUp.Lemmas.StaticDecision

namespace Shuffler.BuildBottomUp

-- buildBottomUp succeeds if and only if StaticSuccess holds. StaticSuccess uses only data from the
-- initial state, and there is no bound on the stack or target length.
theorem buildBottomUp_succeeds_iff_static (initial : State source target spills)
    (h : initial.Valid) :
    (∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial h = .ok ⟨res, trace⟩) ↔ StaticSuccess initial := by
  constructor
  · rintro ⟨res, trace, hrun⟩
    exact (buildBottomUp_static_success_iff initial h).mp ⟨⟨res, trace⟩, hrun, trivial⟩
  · intro hs
    obtain ⟨⟨res, trace⟩, hrun, _⟩ := (buildBottomUp_static_success_iff initial h).mpr hs
    exact ⟨res, trace, hrun⟩

-- If the mapping connects only slots of equal value, buildBottomUp returns the target if and only
-- if StaticSuccess holds.
theorem buildBottomUp_correct_iff_static (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ trace : Trace spills source target,
      buildBottomUp initial h = .ok ⟨target, trace⟩) ↔ StaticSuccess initial := by
  constructor
  · rintro ⟨trace, hrun⟩
    exact (buildBottomUp_succeeds_iff_static initial h).mp ⟨target, trace, hrun⟩
  · intro hs
    obtain ⟨res, trace, hrun⟩ := (buildBottomUp_succeeds_iff_static initial h).mpr hs
    obtain rfl := buildBottomUp_correct_of_ok initial h hmapped hrun
    exact ⟨trace, hrun⟩

end Shuffler.BuildBottomUp
