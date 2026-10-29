module

public import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildBottomUp.Lemmas.LoopProofs

@[expose] public section

namespace Shuffler.Emission

-- A valid initial state satisfies the loop invariant at offset zero.
theorem invariant_initial (initial : State source target spills) (h : initial.Valid) :
    initial.invariant 0 :=
  ⟨h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

-- From a state that satisfies the loop invariant, the loop never fails with an assertion error.
theorem loop_no_assertion (targetOffset : ℕ) (state : State source target spills)
    (inv : state.invariant targetOffset) (reason : String) :
    buildBottomUp.loop targetOffset state ≠ .error (.assertion reason) := by
  intro he
  apply (loop_spec targetOffset state inv).noAssertion reason
  rw [he]
  rfl

-- From a valid initial state, buildBottomUp never fails with an assertion error.
theorem buildBottomUp_no_assertion (initial : State source target spills)
    (h : initial.Valid) (reason : String) :
    buildBottomUp initial h ≠ .error (.assertion reason) := by
  intro he
  apply (buildBottomUp_spec initial h).noAssertion reason
  rw [he]
  rfl

-- From a valid initial state, each error is a blocked error: a needed slot is outside DUP or
-- SWAP reach.
theorem buildBottomUp_error_is_blocked (initial : State source target spills)
    (h : initial.Valid) (he : buildBottomUp initial h = .error err) :
    ∃ blocked, err = .Blocked blocked := by
  apply (buildBottomUp_spec initial h).error
  rw [he]
  rfl

end Shuffler.Emission
