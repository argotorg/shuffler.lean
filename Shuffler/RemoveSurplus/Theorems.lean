module

public import Shuffler.RemoveSurplus.Lemmas
import all Batteries.Tactic.PrintOpaques

import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr

@[expose] public section

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

-- removeSurplus raises no assertion, from any state: every index it reads is in bounds, the slot it
-- swaps with the top is surplus (so not final) and within reach, and it only pops a non-empty stack.
theorem removeSurplus_no_assertion (initial : State source target spills) (reason : String) :
    removeSurplus initial ≠ .error (.assertion reason) := by
  intro he
  apply ((spec_iff_triple _ _).mpr (removeSurplus_triple initial)).noAssertion reason
  rw [he]
  rfl

-- Its only error is a surplus slot out of swap reach.
theorem removeSurplus_error_is_blocked (initial : State source target spills)
    (he : removeSurplus initial = .error err) : ∃ blocked, err = .Blocked blocked := by
  apply ((spec_iff_triple _ _).mpr (removeSurplus_triple initial)).error
  rw [he]
  rfl

-- After removeSurplus, every slot has a destination.
theorem removeSurplus_noSurplus (initial result : State source target spills)
    (h : removeSurplus initial = .ok ⟨none, result⟩) : result.noSurplus := by
  have hs := (spec_iff_triple _ _).mpr (removeSurplus_triple initial)
  simp only [h, completed_ok] at hs
  exact hs.1

-- removeSurplus only ever pops surplus slots: every target offset that had a slot bound to it still
-- has one, holding the same value, and no new binding appears. (A slot equal to the top may take over
-- the top's destination first; the top is then surplus when it is popped.)
theorem removeSurplus_keeps_bindings (initial result : State source target spills)
    (h : removeSurplus initial = .ok ⟨none, result⟩) (dest : Fin target.length) :
    result.boundValue dest = initial.boundValue dest := by
  have hs := (spec_iff_triple _ _).mpr (removeSurplus_triple initial)
  simp only [h, completed_ok] at hs
  exact congrFun hs.2 dest

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

/-- info: 'Shuffler.Emission.removeSurplus_keeps_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms removeSurplus_keeps_bindings

end Shuffler.Emission
