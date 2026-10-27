import Shuffler.BuildMapping.Lemmas
import Batteries.Tactic.PrintOpaques

namespace Shuffler.BuildMapping

-- buildMapping succeeds if and only if `dropped` has one entry per source slot.
theorem buildMapping_ok (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) :
    (∃ mb, buildMapping source target dropped strategy = .ok mb) ↔
      dropped.length = source.length := by
  constructor
  · rintro ⟨mb, h⟩
    by_cases hsizes : dropped.length = source.length
    · exact hsizes
    · simp only [buildMapping, requires, dite_eq_right hsizes] at h
      cases h
  · intro hsizes
    let ⟨mb, h, _⟩ := (buildMapping_succeeds source target dropped strategy hsizes).exists
    exact ⟨mb, h⟩

theorem buildMapping_no_assertion (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) (hsizes : dropped.length = source.length) (reason : String) :
    buildMapping source target dropped strategy ≠ .error (.assertion reason) := by
  obtain ⟨mb, h⟩ := (buildMapping_ok source target dropped strategy).mpr hsizes
  rw [h]
  nofun

-- Audit the whole function, including the passes and `map`.
/-- info: 'Shuffler.BuildMapping.buildMapping' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques buildMapping

/-- info: 'Shuffler.BuildMapping.buildMapping' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping

/-- info: 'Shuffler.BuildMapping.buildMapping_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_ok

/-- info: 'Shuffler.BuildMapping.buildMapping_no_assertion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_no_assertion

end Shuffler.BuildMapping
