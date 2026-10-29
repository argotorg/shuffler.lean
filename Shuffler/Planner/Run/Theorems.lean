module

public import Shuffler.Planner.Run.Defs
import Shuffler.Planner.Run.Lemmas
import all Batteries.Tactic.PrintOpaques
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.Range.Basic
import all Init.Data.List.Sort.Basic
import all Init.Prelude

@[expose] public section

namespace Shuffler.Planner

-- Every run returns a result, including plans that cannot resolve a blocked emission.
theorem run_ok (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool)
    (strategy : BuildMapping.WildcardSlotsStrategy)
    (havailable : ∀ value ∈ target, value.is_junk ∨ value.can_be_freely_generated ∨
      value ∈ source ∨ spills.is_spilled value)
    (hlabels : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel) :
    ∃ result, run source target spills spillingAllowed strategy = .ok result := by
  obtain ⟨result, hr, _⟩ := run_spec source target spills spillingAllowed strategy havailable hlabels
  exact ⟨result, hr⟩

-- The target checks and the progress check hold on every attempt.
theorem run_no_assertion (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool)
    (strategy : BuildMapping.WildcardSlotsStrategy)
    (havailable : ∀ value ∈ target, value.is_junk ∨ value.can_be_freely_generated ∨
      value ∈ source ∨ spills.is_spilled value)
    (hlabels : target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel)
    (reason : String) :
    run source target spills spillingAllowed strategy ≠ .error (.assertion reason) := by
  obtain ⟨result, hr⟩ := run_ok source target spills spillingAllowed strategy havailable hlabels
  rw [hr]
  intro he
  cases he

/-- info: 'Shuffler.Planner.run' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques run

/-- info: 'Shuffler.Planner.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run

/-- info: 'Shuffler.Planner.run_ok' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques run_ok

/-- info: 'Shuffler.Planner.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_ok

/-- info: 'Shuffler.Planner.run_no_assertion' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques run_no_assertion

/-- info: 'Shuffler.Planner.run_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_no_assertion

end Shuffler.Planner
