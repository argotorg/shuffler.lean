import Shuffler.BuildMapping.InPlace
import Batteries.Tactic.PrintOpaques

namespace Shuffler.BuildMapping

-- buildMapping succeeds if and only if `dropped` has one entry per source slot.
theorem buildMapping_ok (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) :
    (∃ result, buildMapping source target dropped strategy = .ok result) ↔
      dropped.length = source.length := by
  constructor
  · rintro ⟨result, h⟩
    by_cases hsizes : dropped.length = source.length
    · exact hsizes
    · simp only [buildMapping, requires, dite_eq_right hsizes] at h
      cases h
  · intro hsizes
    let ⟨result, h, _⟩ := (buildMapping_succeeds source target dropped strategy hsizes).exists
    exact ⟨result, h⟩

theorem buildMapping_no_assertion (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) (hsizes : dropped.length = source.length) (reason : String) :
    buildMapping source target dropped strategy ≠ .error (.assertion reason) := by
  obtain ⟨result, h⟩ := (buildMapping_ok source target dropped strategy).mpr hsizes
  rw [h]
  nofun

-- Every binding uses a source that is not dropped and matches its target value.
theorem buildMapping_valid_of_ok (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result) :
    ∀ s t, result.mapping s = some t →
      dropped[s.val]? = some 0 ∧ SlotMatches source[s] target[t] := by
  have hsizes := (buildMapping_ok source target dropped strategy).mp ⟨result, hrun⟩
  have hvalid := buildMapping_valid source target dropped strategy hsizes
  simpa only [hrun, succeeds_ok] using hvalid

-- Equal values at the same offset stay bound when the source is not dropped.
theorem buildMapping_in_place_of_ok (source target : Stack) (dropped : List Byte)
    (strategy : WildcardSlotsStrategy) {result : BuildMappingResult source target}
    (hrun : buildMapping source target dropped strategy = .ok result)
    (s : Fin source.length) (t : Fin target.length) (hpos : s.val = t.val)
    (hvalue : source[s] = target[t]) (hdrop : dropped[s.val]? = some 0) :
    result.mapping s = some t := by
  have hsizes := (buildMapping_ok source target dropped strategy).mp ⟨result, hrun⟩
  have hbound := buildMapping_succeeds_in_place source target dropped strategy hsizes
    s t hpos hvalue hdrop
  simpa only [hrun, succeeds_ok] using hbound

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

/-- info: 'Shuffler.BuildMapping.buildMapping_valid_of_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_valid_of_ok

/-- info: 'Shuffler.BuildMapping.buildMapping_in_place_of_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_in_place_of_ok

end Shuffler.BuildMapping
