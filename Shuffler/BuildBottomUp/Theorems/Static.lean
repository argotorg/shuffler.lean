module

public import Shuffler.BuildBottomUp.Lemmas.StaticDecision
import Shuffler.BuildBottomUp.Lemmas.StaticProof
import Shuffler.BuildBottomUp.Theorems.Correctness

@[expose] public section

namespace Shuffler.Emission

-- buildBottomUp succeeds if and only if StaticSuccess holds. StaticSuccess uses only data from the
-- initial state, and there is no bound on the stack or target length.
theorem buildBottomUp_succeeds_iff_static (initial : State source target spills)
    (h : initial.Valid) :
    (∃ result : State source target spills, buildBottomUp initial h = .ok ⟨none, result⟩) ↔
      StaticSuccess initial := by
  constructor
  · rintro ⟨result, hrun⟩
    exact (buildBottomUp_static_success_iff initial h).mp
      ⟨_, completedTrace_of_ok hrun, trivial⟩
  · intro hs
    obtain ⟨value, heq, _⟩ := (buildBottomUp_static_success_iff initial h).mpr hs
    obtain ⟨result, hrun, _⟩ := completedTrace_ok_inversion heq
    exact ⟨result, hrun⟩

-- If the mapping connects only slots of equal value, buildBottomUp returns the target if and only
-- if StaticSuccess holds.
theorem buildBottomUp_correct_iff_static (initial : State source target spills)
    (h : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    (∃ result : State source target spills,
      buildBottomUp initial h = .ok ⟨none, result⟩ ∧ result.stack = target) ↔ StaticSuccess initial := by
  constructor
  · rintro ⟨result, hrun, _⟩
    exact (buildBottomUp_succeeds_iff_static initial h).mp ⟨result, hrun⟩
  · intro hs
    obtain ⟨result, hrun⟩ := (buildBottomUp_succeeds_iff_static initial h).mpr hs
    exact ⟨result, hrun, buildBottomUp_correct_of_ok initial h hmapped hrun⟩

end Shuffler.Emission
