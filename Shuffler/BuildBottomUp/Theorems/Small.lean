module

public import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildBottomUp.Lemmas.SuccessProofs
import Shuffler.BuildBottomUp.Theorems.Correctness

@[expose] public section

namespace Shuffler.Emission

-- buildBottomUp always succeeds on a valid initial stack of at most 16 slots, for a target of any
-- length.
theorem buildBottomUp_succeeds_small (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    ∃ result : State source target spills, buildBottomUp initial h = .ok ⟨none, result⟩ := by
  obtain ⟨value, heq, _⟩ := buildBottomUp_success initial h hsmall
  obtain ⟨result, hrun, _⟩ := completedTrace_ok_inversion heq
  exact ⟨result, hrun⟩

-- For an initial stack of at most 16 slots, if the mapping connects only slots of equal value,
-- buildBottomUp always returns the target.
theorem buildBottomUp_correct_within_dup_reach (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ result : State source target spills,
      buildBottomUp initial h = .ok ⟨none, result⟩ ∧ result.stack = target := by
  obtain ⟨result, hrun⟩ := buildBottomUp_succeeds_small initial h hsmall
  exact ⟨result, hrun, buildBottomUp_correct_of_ok initial h hmapped hrun⟩

-- The same result for an initial stack of at most 14 slots.
theorem buildBottomUp_correct_small (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length < MAX_DUP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ result : State source target spills,
      buildBottomUp initial h = .ok ⟨none, result⟩ ∧ result.stack = target :=
  buildBottomUp_correct_within_dup_reach initial h (by omega) hmapped

end Shuffler.Emission
