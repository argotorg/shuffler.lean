import Shuffler.BuildBottomUp.Defs
import Shuffler.BuildBottomUp.Lemmas.LoopProofs
import Batteries.Tactic.PrintOpaques

namespace Shuffler.BuildBottomUp

-- Valid states have the required size, pending count, and available target values.
-- Operations outside DUP or SWAP reach can still return a blocked error.
theorem buildBottomUp_no_assertion (initial : State source target spills)
    (h : initial.Valid) (reason : String) :
    buildBottomUp initial ≠ .error (.assertion reason) :=
  (buildBottomUp_spec initial h).noAssertion reason

theorem buildBottomUp_error_is_blocked (initial : State source target spills)
    (h : initial.Valid) (he : buildBottomUp initial = .error err) :
    ∃ excess, err = .blocked excess :=
  (buildBottomUp_spec initial h).error he

-- Audit the whole function, including the recursion and the action helpers.
/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_no_assertion

end Shuffler.BuildBottomUp
