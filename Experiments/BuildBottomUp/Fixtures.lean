import Experiments.BuildBottomUp.Independence

check_no_legacy_imports

namespace BuildBottomUpExperiments.Checked

-- Adapt the existing branch fixtures to the checked wrapper's grouped input proof.
def runFixture (cursor : ℕ) (state : State source target spills)
    (processed : Processed cursor state)
    (size : state.stack.length + state.pending_generations = target.length)
    (pending : state.mapping.unmapped_target_slots = state.pending_generations)
    (available : ∀ i, state.isAvailable i) : Except ShuffleErr (Result source spills) :=
  buildBottomUpVerified cursor state ⟨processed, size, pending, available⟩

end BuildBottomUpExperiments.Checked
