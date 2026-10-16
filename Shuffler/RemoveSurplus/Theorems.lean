import Shuffler.RemoveSurplus.Lemmas
import Batteries.Tactic.PrintOpaques

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

-- removeSurplus raises no assertion, from any state: every index it reads is in bounds, the slot it
-- swaps with the top is surplus (so not final) and within reach, and it only pops a non-empty stack.
theorem removeSurplus_no_assertion (initial : State source target spills) (reason : String) :
    removeSurplus initial ≠ .error (.assertion reason) :=
  ((spec_iff_triple _ _).mpr (removeSurplus_triple initial)).noAssertion reason

-- Its only error is a surplus slot out of swap reach.
theorem removeSurplus_error_is_blocked (initial : State source target spills)
    (he : removeSurplus initial = .error err) : ∃ excess, err = .blocked excess :=
  ((spec_iff_triple _ _).mpr (removeSurplus_triple initial)).error he

-- After removeSurplus, every slot has a destination.
theorem removeSurplus_noSurplus (initial result : State source target spills)
    (h : removeSurplus initial = .ok result) : result.noSurplus := by
  have hs := (spec_iff_triple _ _).mpr (removeSurplus_triple initial)
  rw [h] at hs
  exact hs

-- Audit the whole function, including the loops and the actions.
/-- info: 'Shuffler.Emission.removeSurplus' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques removeSurplus

/-- info: 'Shuffler.Emission.removeSurplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms removeSurplus

/-- info: 'Shuffler.Emission.removeSurplus_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms removeSurplus_no_assertion

/-- info: 'Shuffler.Emission.removeSurplus_noSurplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms removeSurplus_noSurplus

end Shuffler.Emission
