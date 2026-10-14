import Shuffler.BuildBottomUp.Theorems.Correctness
import Shuffler.BuildBottomUp.Lemmas.SuccessProofs

namespace Shuffler.BuildBottomUp

-- buildBottomUp always succeeds on a valid initial stack of at most 16 slots, for a target of any
-- length.
theorem buildBottomUp_succeeds_small (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    ∃ (res : Stack) (trace : Trace spills source res),
      buildBottomUp initial h = .ok ⟨res, trace⟩ := by
  obtain ⟨⟨res, trace⟩, heq, _⟩ := buildBottomUp_success initial h hsmall
  exact ⟨res, trace, heq⟩

-- For an initial stack of at most 16 slots, if the mapping connects only slots of equal value,
-- buildBottomUp always returns the target.
theorem buildBottomUp_correct_within_dup_reach (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target, buildBottomUp initial h = .ok ⟨target, trace⟩ := by
  obtain ⟨res, trace, heq⟩ := buildBottomUp_succeeds_small initial h hsmall
  obtain rfl := buildBottomUp_correct_of_ok initial h hmapped heq
  exact ⟨trace, heq⟩

-- The same result for an initial stack of at most 14 slots.
theorem buildBottomUp_correct_small (initial : State source target spills)
    (h : initial.Valid) (hsmall : initial.stack.length < MAX_DUP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target, buildBottomUp initial h = .ok ⟨target, trace⟩ :=
  buildBottomUp_correct_within_dup_reach initial h (by omega) hmapped

end Shuffler.BuildBottomUp
