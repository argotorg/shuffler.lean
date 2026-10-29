module

public import Shuffler.Resolve.Properties
public import Shuffler.Resolve.Defs
public import Std.WP.Triple.Basic
public import Std.WP.Monad.Instances
import Shuffler.Resolve.Lemmas
import Std.WP.Triple.SpecLemmas
import all Batteries.Tactic.PrintOpaques

@[expose] public section

open Std.WP
set_option experimental.vcgen true

namespace Shuffler.Planner

variable {source target : Stack}

theorem classify_not_label (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length) (cls : ℕ)
    (hclass : classify state mapping droppedNow offset = .ok (some cls)) :
    ¬source[offset].isFunctionReturnLabel := by
  intro hlabel
  simp only [Fin.getElem_fin] at hlabel
  simp [classify, hlabel, pure, Except.pure] at hclass

theorem labelsUndropped_drop (state : State source target) (h : state.LabelsUndropped)
    (offset : Fin source.length) (hlabel : ¬source[offset].isFunctionReturnLabel) (spills : SpillSet) :
    State.LabelsUndropped (target := target)
      { state with spills, dropped := state.dropped.set offset 1 } := by
  intro i hi
  have hne : i ≠ offset := by intro heq; subst i; exact hlabel hi
  simpa [Vector.getElem_set, Fin.val_ne_of_ne (Ne.symm hne)] using h i hi

attribute [local spec] classify_spec spill_add_spec resolve_requires_spec

theorem resolve_labelsUndropped_triple (initial : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) :
    ⦃initial.LabelsUndropped⦄ resolve initial mapping blocked current
    ⦃fun result => result.2.LabelsUndropped; fun _ => True⦄ := by
  refine ⟨fun hinitial => ?_⟩
  unfold resolve
  dsimp only
  refine (Triple.bind _ _ _ (resolve_candidates_triple mapping blocked current)
    fun candidates => ?_).le_wp trivial
  vcgen
  case inv1 =>
    exact fun _ _ s => s.2.1.LabelsUndropped ∧
      ∀ r, s.1 = some r → r.2.LabelsUndropped
  case inv2 =>
    rename_i state droppedNow _
    exact fun _ _ found => Selected state mapping droppedNow candidates found
  all_goals dsimp at *
  all_goals try simp_all
  all_goals try first
    | exact Selected.start _ _ _ _
    | exact Selected.select _ _ _ _ _ (by simp) (by assumption) (by assumption) _
    | exact Selected.four (by assumption) _ rfl
    | exact Option.isSome_iff_ne_none.mpr (by assumption)
    | exact RetainedCandidates.current (by assumption)
  all_goals
    apply labelsUndropped_drop
    · exact (show _ ∧ _ from by assumption).1
    · apply classify_not_label
      exact (Selected.get (by assumption) _).2.2

theorem resolve_preserves_labelsUndropped (initial result : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) (success : Bool)
    (hlabels : initial.LabelsUndropped)
    (hresolve : resolve initial mapping blocked current = .ok (success, result)) :
    result.LabelsUndropped := by
  have hs := (resolve_labelsUndropped_triple initial mapping blocked current).le_wp hlabels
  rw [hresolve] at hs
  exact hs

/-- info: 'Shuffler.Planner.resolve_preserves_labelsUndropped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolve_preserves_labelsUndropped

/-- info: 'Shuffler.Planner.resolve_preserves_labelsUndropped' does not use any opaque or partial definitions -/
#guard_msgs in
#print opaques resolve_preserves_labelsUndropped

end Shuffler.Planner
