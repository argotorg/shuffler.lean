module

public import Shuffler.Planner.Run.Defs
public import Shuffler.BuildMapping.Theorems
public import Shuffler.BuildMapping.Lemmas.Availability
public import Shuffler.Resolve.Theorems
public import Shuffler.Emission.Run.Lemmas.Execution

@[expose] public section

namespace Shuffler.Planner

variable {source target : Stack}

theorem buildMapping_retainedUndropped (current : State source target)
    (strategy : BuildMapping.WildcardSlotsStrategy)
    {builder : BuildMapping.BuildMappingResult source target}
    (hbuilder : BuildMapping.buildMapping source target current.dropped.toList strategy = .ok builder) :
    current.RetainedUndropped builder.mapping := by
  intro i hi
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hi
  have hdrop := (BuildMapping.buildMapping_valid_of_ok source target _ strategy hbuilder i j hj).1
  simpa [Vector.getElem?_toList, i.isLt] using hdrop

theorem buildMapping_available (current : State source target)
    (strategy : BuildMapping.WildcardSlotsStrategy)
    {builder : BuildMapping.BuildMappingResult source target}
    (hbuilder : BuildMapping.buildMapping source target current.dropped.toList strategy = .ok builder)
    (havailable : current.TargetAvailable) :
    ∀ j : Fin target.length, target[j].can_be_freely_generated ∨
      current.spills.is_spilled target[j] ∨
      ∃ i dest, builder.mapping i = some dest ∧ source[i] = target[j] := by
  intro j
  by_cases hj : target[j].is_junk
  · exact Or.inl (Value.can_be_freely_generated_of_is_junk _ hj)
  rcases havailable target[j] (List.getElem_mem j.isLt) hj with hg | hs | ⟨i, hd, hv⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl hs)
  · apply Or.inr ∘ Or.inr
    exact BuildMapping.buildMapping_available_of_ok source target _ strategy hbuilder i j
      (by simpa [Vector.getElem?_toList, i.isLt] using hd) hv hj

theorem loop_spec (source target : Stack) (strategy : BuildMapping.WildcardSlotsStrategy)
    (current : State source target) (sawWildcardCopy : Bool)
    (havailable : current.TargetAvailable) :
    ∃ result, run.loop source target strategy current sawWildcardCopy = .ok result ∧
      result.state.TargetAvailable := by
  refine run.loop.induct source target
    (motive := fun current sawWildcardCopy => current.TargetAvailable →
      ∃ result, run.loop source target strategy current sawWildcardCopy = .ok result ∧
        result.state.TargetAvailable) ?_ current sawWildcardCopy havailable
  intro current sawWildcardCopy
  dsimp only
  intro ih havailable
  obtain ⟨builder, hbuilder⟩ := (BuildMapping.buildMapping_ok source target
    current.dropped.toList strategy).mpr (by simp)
  have hretained := buildMapping_retainedUndropped current strategy hbuilder
  obtain ⟨emitted, hemitted, _, hpositive⟩ := Emission.run_spec source target builder.mapping
    current.spills (buildMapping_available current strategy hbuilder havailable)
  rw [run.loop.eq_1, hbuilder, except_ok_bind]
  dsimp only
  rw [hemitted, except_ok_bind]
  cases hblocked : emitted.blocked with
  | none => exact ⟨_, rfl, havailable⟩
  | some blocked =>
    obtain ⟨⟨success, resolved⟩, hresolved⟩ := resolve_ok current builder.mapping blocked emitted.state.mapping
    have hravailable := resolve_preserves_target_available current resolved builder.mapping blocked
      emitted.state.mapping success havailable hretained hresolved
    simp only [hresolved, except_ok_bind]
    cases success with
    | false => exact ⟨_, rfl, hravailable⟩
    | true =>
      have hprogress := resolve_remaining_strict current resolved builder.mapping blocked
        emitted.state.mapping hretained hresolved (hpositive blocked hblocked)
      simp only [not_true_eq_false, ↓reduceIte,
        requires_of_true _ hprogress, except_ok_bind]
      exact ih builder resolved hprogress hravailable

theorem run_spec (source target : Stack) (spills : SpillSet) (spillingAllowed : Bool)
    (strategy : BuildMapping.WildcardSlotsStrategy)
    (havailable : ∀ value ∈ target, value.is_junk ∨ value.can_be_freely_generated ∨
      value ∈ source ∨ spills.is_spilled value) :
    ∃ result, run source target spills spillingAllowed strategy = .ok result ∧
      result.state.TargetAvailable := by
  have hchecks : (forIn target PUnit.unit fun slot _ => do
      _ ← requires (slot.is_junk ∨ slot.can_be_freely_generated ∨ slot ∈ source ∨ spills.is_spilled slot)
        "target slot neither on the stack nor generatable"
      pure (.yield PUnit.unit) : Except ShuffleErr PUnit) = .ok PUnit.unit := by
    induction target with
    | nil => rfl
    | cons value rest ih =>
      simp only [List.forIn_cons, requires_of_true _ (havailable value (by simp)),
        except_ok_bind, pure_bind]
      exact ih (fun value hv => havailable value (by simp [hv]))
  let initial : State source target := {
    spills, spillingAllowed, dropped := Vector.replicate source.length 0 }
  have hinitial : initial.TargetAvailable := by
    intro value hmem hnonjunk
    rcases havailable value hmem with hj | hg | hs | hspill
    · exact (hnonjunk hj).elim
    · exact Or.inl hg
    · obtain ⟨i, hi, hv⟩ := List.getElem_of_mem hs
      exact Or.inr (Or.inr ⟨⟨i, hi⟩, by simp [initial], hv⟩)
    · exact Or.inr (Or.inl hspill)
  obtain ⟨result, hresult, hr⟩ := loop_spec source target strategy initial false hinitial
  refine ⟨result, ?_, hr⟩
  unfold run
  rw [hchecks, except_ok_bind]
  exact hresult

end Shuffler.Planner
