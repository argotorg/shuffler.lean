module

public import Shuffler.BuildMapping.Lemmas.Strategies.Compare
import Shuffler.BuildMapping.Lemmas.Strategies.Prefix
import Shuffler.BuildMapping.Lemmas.Strategies.Suffix

@[expose] public section

namespace Shuffler.BuildMapping.Strategies

variable {source target : Stack}

-- The last two passes preserve agreement or the target that distinguishes the mappings.
theorem suffix_compared (left right : MappingBuilder source target) (h : Compared left right) :
    Both (suffix left) (suffix right) Compared := by
  rcases h with ⟨hleft, hright, hequal | hdifferent⟩
  · rcases hequal with ⟨rfl, hflag⟩
    obtain ⟨result, hrun, hsize, hflag', _⟩ := (suffix_succeeds left hleft).exists
    rw [hrun]
    exact ⟨hsize, hsize, Or.inl ⟨rfl, hflag'.trans hflag⟩⟩
  · rcases hdifferent with ⟨hflagL, hflagR, t, s, hwild, hlabel, hfree, hbound⟩
    refine (suffix_succeeds left hleft).mono fun left' hl => ?_
    refine (suffix_succeeds right hright).mono fun right' hr => ?_
    exact ⟨hl.1, hr.1, Or.inr ⟨hl.2.1.trans hflagL, hr.2.1.trans hflagR,
      t, s, hwild, hlabel, (hl.2.2 t hwild).trans hfree, (hr.2.2 t hwild).trans hbound⟩⟩

private theorem compared_properties (left right : MappingBuilder source target)
    (h : Compared left right) :
    left.sawWildcardCopy = right.sawWildcardCopy ∧
    (left.mapping = right.mapping ↔ left.sawWildcardCopy = false) ∧
    (left.sawWildcardCopy = true → Different left right) := by
  rcases h with ⟨_, _, hequal | hdifferent⟩
  · rcases hequal with ⟨rfl, hflag⟩
    refine ⟨rfl, ⟨fun _ => hflag, fun _ => rfl⟩, ?_⟩
    intro htrue
    rw [hflag] at htrue
    cases htrue
  · rcases hdifferent with ⟨hflagL, hflagR, hdifferent⟩
    refine ⟨hflagL.trans hflagR.symm, ⟨?_, ?_⟩, fun _ => hdifferent⟩
    · intro hmaps
      obtain ⟨t, s, _, _, hfree, hbound⟩ := hdifferent
      rw [hmaps, hbound] at hfree
      cases hfree
    · intro hfalse
      rw [hflagL] at hfalse
      cases hfalse

-- Both strategies report the same flag. A true flag records a target on which they differ.
theorem buildMapping_comparison (source target : Stack) (dropped : List Byte)
    (hsizes : dropped.length = source.length) :
    Both (buildMapping source target dropped .Leave) (buildMapping source target dropped .Take)
      fun left right =>
        left.sawWildcardCopy = right.sawWildcardCopy ∧
        (left.mapping = right.mapping ↔ left.sawWildcardCopy = false) ∧
        (left.sawWildcardCopy = true → ∃ t s,
          ¬ target[t].is_junk ∧ ¬ target[t].isFunctionReturnLabel ∧
          left.mapping.symm t = none ∧ right.mapping.symm t = some s) := by
  obtain ⟨initial, hprefix, hdropped, hflag⟩ :=
    (prefix_succeeds source target dropped hsizes).exists
  have hsize : initial.dropped.length = source.length := hdropped ▸ hsizes
  have hinitial : Compared initial initial := ⟨hsize, hsize, Or.inl ⟨rfl, hflag⟩⟩
  simp only [buildMapping_eq_phases, requires_of_true _ hsizes, except_ok_bind, hprefix]
  refine (copyPass_compared initial initial hinitial).bind fun left right hcompared => ?_
  refine (suffix_compared left right hcompared).bind fun left' right' hfinal => ?_
  exact compared_properties left' right' hfinal

-- Extract the comparison properties from two successful production runs.
theorem comparison_of_ok (source target : Stack) (dropped : List Byte)
    {leave take : BuildMappingResult source target}
    (hleave : buildMapping source target dropped .Leave = .ok leave)
    (htake : buildMapping source target dropped .Take = .ok take) :
    leave.sawWildcardCopy = take.sawWildcardCopy ∧
      (leave.mapping = take.mapping ↔ leave.sawWildcardCopy = false) ∧
      (leave.sawWildcardCopy = true → ∃ t s,
        ¬ target[t].is_junk ∧ ¬ target[t].isFunctionReturnLabel ∧
        leave.mapping.symm t = none ∧ take.mapping.symm t = some s) := by
  have hsizes : dropped.length = source.length := by
    by_cases hsizes : dropped.length = source.length
    · exact hsizes
    · simp only [buildMapping, requires, dite_eq_right hsizes] at hleave
      cases hleave
  have h := buildMapping_comparison source target dropped hsizes
  simpa only [Both, hleave, htake, succeeds_ok] using h

end Shuffler.BuildMapping.Strategies
