import Shuffler.BuildMapping.Defs
import Shuffler.BuildMapping.Lemmas.InPlace
import Shuffler.BuildMapping.Lemmas.Strategies.Proof
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

-- The choice of strategy does not change whether an optional wildcard copy was seen.
theorem buildMapping_sawWildcardCopy_eq (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take) :
    leave.sawWildcardCopy = take.sawWildcardCopy :=
  (Strategies.comparison_of_ok source target dropped hleave htake).1

-- The mappings agree exactly when the strategy had no optional copy to take.
theorem buildMapping_mapping_eq_iff (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take) :
    leave.mapping = take.mapping ↔ leave.sawWildcardCopy = false :=
  (Strategies.comparison_of_ok source target dropped hleave htake).2.1

-- A true flag identifies a target that Take binds and Leave keeps unbound.
theorem buildMapping_differs_of_sawWildcardCopy (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take)
    (hflag : leave.sawWildcardCopy = true) :
    ∃ t s, ¬ target[t].is_junk ∧ ¬ target[t].isFunctionReturnLabel ∧
      leave.mapping.symm t = none ∧ take.mapping.symm t = some s :=
  (Strategies.comparison_of_ok source target dropped hleave htake).2.2 hflag

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

/-- info: 'Shuffler.BuildMapping.buildMapping_sawWildcardCopy_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_sawWildcardCopy_eq

/-- info: 'Shuffler.BuildMapping.buildMapping_mapping_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_mapping_eq_iff

/-- info: 'Shuffler.BuildMapping.buildMapping_differs_of_sawWildcardCopy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms buildMapping_differs_of_sawWildcardCopy

end Shuffler.BuildMapping
