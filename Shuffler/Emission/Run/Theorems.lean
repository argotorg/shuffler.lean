module

public import Shuffler.Emission.Run.Defs
import Shuffler.Emission.Run.Lemmas.Execution
import all Batteries.Tactic.PrintOpaques
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.Range.Basic
import all Init.Data.List.Sort.Basic
import all Init.Prelude

@[expose] public section

namespace Shuffler.Emission

-- Each target value can be generated, loaded, or copied from a retained source slot.
-- Function return labels must already have a bound source.
-- Every attempt returns its state, including when an operation is blocked.
theorem run_ok (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet)
    (havailable : ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      spills.is_spilled target[j] ∨ ∃ i dest, mapping i = some dest ∧ source[i] = target[j])
    (hlabels : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (mapping.symm j).isSome) :
    ∃ result, run source target mapping spills = .ok result := by
  obtain ⟨result, hr, _⟩ := run_spec source target mapping spills havailable hlabels
  exact ⟨result, hr⟩

theorem run_no_assertion (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet)
    (havailable : ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      spills.is_spilled target[j] ∨ ∃ i dest, mapping i = some dest ∧ source[i] = target[j])
    (hlabels : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (mapping.symm j).isSome)
    (reason : String) : run source target mapping spills ≠ .error (.assertion reason) := by
  obtain ⟨result, hr⟩ := run_ok source target mapping spills havailable hlabels
  simp [hr]

theorem run_blocked_positive (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet)
    (havailable : ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      spills.is_spilled target[j] ∨ ∃ i dest, mapping i = some dest ∧ source[i] = target[j])
    (hlabels : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (mapping.symm j).isSome)
    {result : Result source target spills} {blocked : Blocked}
    (hrun : run source target mapping spills = .ok result)
    (hblocked : result.blocked = some blocked) : 0 < blocked.excess := by
  obtain ⟨actual, hr, _, hp⟩ := run_spec source target mapping spills havailable hlabels
  cases hrun.symm.trans hr
  exact hp blocked hblocked

theorem run_planned_mapping (source target : Stack) (mapping : Mapping source.length target.length)
    (spills : SpillSet)
    (havailable : ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      spills.is_spilled target[j] ∨ ∃ i dest, mapping i = some dest ∧ source[i] = target[j])
    (hlabels : ∀ j : Fin target.length, target[j].isFunctionReturnLabel → (mapping.symm j).isSome)
    {result : Result source target spills} (hrun : run source target mapping spills = .ok result) :
    result.state.planned_mapping = mapping := by
  obtain ⟨actual, hr, hp, _⟩ := run_spec source target mapping spills havailable hlabels
  cases hrun.symm.trans hr
  exact hp

/-- info: 'Shuffler.Emission.run' depends on opaque or partial definitions: [String.Internal.append] -/
#guard_msgs in
#print opaques run

/-- info: 'Shuffler.Emission.run_no_assertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_no_assertion

/-- info: 'Shuffler.Emission.run_blocked_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_blocked_positive

end Shuffler.Emission
