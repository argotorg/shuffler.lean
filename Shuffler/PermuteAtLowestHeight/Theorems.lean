module

public import Shuffler.PermuteAtLowestHeight.Lemmas
import all Batteries.Tactic.PrintOpaques
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Prelude

@[expose] public section

namespace Shuffler.PermuteAtLowestHeight

open Emission

variable {source target : Stack} {spills : SpillSet}

theorem permuteAtLowestHeight_no_assertion (state : State source target spills)
    (htotal : ∀ i, (state.mapping.destinationOf i).isSome)
    (hdom : ∀ j, (state.mapping.symm j).isSome = (state.planned_mapping.symm j).isSome)
    (reason : String) :
    permuteAtLowestHeight state ≠ .error (.assertion reason) := by
  obtain ⟨result, hr, _⟩ := permuteAtLowestHeight_result_spec state htotal hdom
  rw [hr]
  intro he
  cases he

/-- info: 'Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques permuteAtLowestHeight

/-- info: 'Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms permuteAtLowestHeight

/-- info: 'Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight_no_assertion' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques permuteAtLowestHeight_no_assertion

/-- info: 'Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight_no_assertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms permuteAtLowestHeight_no_assertion

end Shuffler.PermuteAtLowestHeight
