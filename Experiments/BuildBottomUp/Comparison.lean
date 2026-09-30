import Experiments.BuildBottomUp.Equivalence
import Experiments.BuildBottomUp.Deferred
import Experiments.BuildBottomUp.Observations

namespace BuildBottomUpExperiments

-- Used by the existing branch fixtures. A difference, including a new assertion
-- error, makes both their success checks and their Blocked checks fail.
def compareAndRun (cursor : ℕ) (state : State source target spills)
    (hinv : LoopInvariant cursor state)
    (hsize : state.stack.length + state.pending_generations = target.length)
    (hpending : state.mapping.unmapped_target_slots = state.pending_generations)
    (havailable : ∀ i, state.is_available i) : Checked.M (Checked.Result source spills) :=
  let original := Checked.liftResult (build_bottom_up cursor state hinv hsize hpending havailable)
  let deferred := Checked.liftResult (Deferred.buildBottomUp cursor state ⟨hinv, hsize, hpending, havailable⟩)
  let checked := Checked.buildBottomUp cursor state
  let verified := Checked.liftResult
    (Checked.buildBottomUpVerified cursor state ⟨hinv, hsize, hpending, havailable⟩)
  if observe original = observe deferred ∧ observe original = observe checked ∧
      observe original = observe verified then checked
  else .error (.assertion "build-bottom-up results differ")

end BuildBottomUpExperiments
