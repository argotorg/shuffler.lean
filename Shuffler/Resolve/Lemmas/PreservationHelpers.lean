module

public import Shuffler.Resolve.Properties
public import Shuffler.Resolve.Defs
import Shuffler.Resolve.Lemmas
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP

set_option experimental.vcgen true

namespace Shuffler.Planner

variable {source target : Stack}

-- A reported copy is distinct, retained, equal, and not dropped during this call.
theorem otherRetainedCopy_exists (mapping : Mapping source.length target.length)
    (droppedNow : Vector Byte source.length) (offset : Fin source.length)
    (h : hasOtherRetainedCopy source mapping droppedNow offset = true) :
    ∃ other : Fin source.length, other ≠ offset ∧ source[other] = source[offset] ∧
      (mapping.destinationOf other).isSome ∧ droppedNow[other] = 0 := by
  have hs : ⦃True⦄ (show Id Bool from hasOtherRetainedCopy source mapping droppedNow offset)
      ⦃fun result => result = true → ∃ other : Fin source.length,
        other ≠ offset ∧ source[other] = source[offset] ∧
          (mapping.destinationOf other).isSome ∧ droppedNow[other] = 0⦄ := by
    unfold hasOtherRetainedCopy Id.run
    vcgen
    case inv1 =>
      exact fun _ _ result => result.1 = some true → ∃ other : Fin source.length,
        other ≠ offset ∧ source[other] = source[offset] ∧
          (Mapping.destinationOf mapping other).isSome ∧ droppedNow[other] = 0
    all_goals simp_all [isRetained]
    all_goals aesop
  have hh := hs.le_wp trivial
  exact hh h

theorem isDemanded_of_mem (value : Value) (hmem : value ∈ target) (hjunk : ¬ value.is_junk) :
    isDemanded target value = true := by
  simp only [isDemanded, List.any_eq_true]
  exact ⟨value, hmem, by simp [hjunk]⟩

-- An accepted class either preserves the value by one of these means or requests a new spill.
theorem classify_drop_safe (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length) (cls : ℕ)
    (h : classify state mapping droppedNow offset = .ok (some cls)) :
    ¬ isDemanded target source[offset] ∨ source[offset].can_be_freely_generated ∨
      state.spills.is_spilled source[offset] ∨
      hasOtherRetainedCopy source mapping droppedNow offset ∨ cls = 4 := by
  simp only [classify] at h
  split at h
  · simp [pure, Except.pure] at h
  · rename_i hlabel
    unfold requires at h
    split at h
    · rename_i hbound
      simp only [pure, Except.pure, except_ok_bind] at h
      split at h
      · rename_i hzero
        rcases hzero.2 with hregen | hnot
        · rcases hregen with hjunk | hfree | hspill | hother
          · exact Or.inr (Or.inl (Value.can_be_freely_generated_of_is_junk _ hjunk))
          · exact Or.inr (Or.inl hfree)
          · exact Or.inr (Or.inr (Or.inl hspill))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hother)))
        · exact Or.inl hnot
      · split at h
        · rename_i hfree; exact Or.inr (Or.inl hfree)
        · split at h
          · rename_i hspill; exact Or.inr (Or.inr (Or.inl hspill))
          · split at h
            · rename_i hother; exact Or.inr (Or.inr (Or.inr (Or.inl hother)))
            · split at h
              · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa using h.symm))))
              · simp at h
    · simp [throw, bind, Except.bind] at h

-- A retained copy not dropped during this call remains available in the current state.
def DropCompatible (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length) : Prop :=
  ∀ i, (mapping.destinationOf i).isSome → droppedNow[i] = 0 → state.dropped[i] = 0

theorem dropCompatible_start (state : State source target)
    (mapping : Mapping source.length target.length) (h : state.RetainedUndropped mapping) :
    DropCompatible state mapping (Vector.replicate source.length 0) := by
  intro i hi _
  exact h i hi

theorem dropCompatible_set (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (h : DropCompatible state mapping droppedNow) (offset : Fin source.length) (spills : SpillSet) :
    DropCompatible { state with spills, dropped := state.dropped.set offset 1 }
      mapping (droppedNow.set offset 1) := by
  intro i hi hz
  by_cases heq : i = offset
  · subst i
    simp at hz
  · simpa [Vector.getElem_set, Fin.val_ne_of_ne (Ne.symm heq)] using
      h i hi (by simpa [Vector.getElem_set, Fin.val_ne_of_ne (Ne.symm heq)] using hz)

-- Dropping the selected slot preserves every required value, after adding any required spill.
theorem targetAvailable_drop (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (havailable : state.TargetAvailable) (hcompatible : DropCompatible state mapping droppedNow)
    (offset : Fin source.length) (cls : ℕ)
    (hclass : classify state mapping droppedNow offset = .ok (some cls))
    (spills : SpillSet) (hspills : ∀ value, state.spills.is_spilled value → spills.is_spilled value)
    (hnew : cls = 4 → spills.is_spilled source[offset]) :
    State.TargetAvailable (target := target)
      { state with spills, dropped := state.dropped.set offset 1 } := by
  intro value hmem hjunk
  rcases havailable value hmem hjunk with hfree | hspill | ⟨i, hizero, hivalue⟩
  · exact Or.inl hfree
  · exact Or.inr (Or.inl (hspills value hspill))
  · by_cases heq : i = offset
    · subst i
      obtain hnot | hfree | hspill | hcopy | hfour :=
        classify_drop_safe state mapping droppedNow offset cls hclass
      · exact (hnot (by simpa [hivalue] using isDemanded_of_mem value hmem hjunk)).elim
      · exact Or.inl (hivalue ▸ hfree)
      · exact Or.inr (Or.inl (hspills value (hivalue ▸ hspill)))
      · obtain ⟨other, hne, hequal, hretained, hzero⟩ :=
          otherRetainedCopy_exists mapping droppedNow offset hcopy
        refine Or.inr (Or.inr ⟨other, ?_, hequal.trans hivalue⟩)
        simpa [Vector.getElem_set, Fin.val_ne_of_ne (Ne.symm hne)] using
          hcompatible other hretained hzero
      · exact Or.inr (Or.inl (hivalue ▸ hnew hfour))
    · refine Or.inr (Or.inr ⟨i, ?_, hivalue⟩)
      simpa [Vector.getElem_set, Fin.val_ne_of_ne (Ne.symm heq)] using hizero

end Shuffler.Planner
