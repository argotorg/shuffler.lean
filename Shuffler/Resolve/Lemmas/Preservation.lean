import Shuffler.Resolve.Lemmas
import Shuffler.Resolve.Lemmas.PreservationHelpers

open Std.Do

set_option mvcgen.warning false

namespace Shuffler.Planner

attribute [local spec] classify_spec spill_add_spec resolve_requires_spec

variable {source target : Stack}

private theorem selected_drop_preserves (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (candidates : List (Fin source.length)) (found : Option (Fin source.length) × ℕ)
    (hselected : Selected state mapping droppedNow candidates found) (hsome : found.1.isSome)
    (havailable : state.TargetAvailable) (hcompatible : DropCompatible state mapping droppedNow)
    (hfour : found.2 ≠ 4) :
    State.TargetAvailable (target := target) { state with dropped := state.dropped.set (found.1.get hsome) 1 } ∧
    DropCompatible { state with dropped := state.dropped.set (found.1.get hsome) 1 }
      mapping (droppedNow.set (found.1.get hsome) 1) := by
  constructor
  · exact targetAvailable_drop state mapping droppedNow havailable hcompatible _ _
      (hselected.get hsome).2.2 state.spills (fun _ h => h) (fun h => (hfour h).elim)
  · exact dropCompatible_set state mapping droppedNow hcompatible _ state.spills

private theorem selected_spill_drop_preserves (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (candidates : List (Fin source.length)) (found : Option (Fin source.length) × ℕ)
    (hselected : Selected state mapping droppedNow candidates found) (hsome : found.1.isSome)
    (havailable : state.TargetAvailable) (hcompatible : DropCompatible state mapping droppedNow)
    (spills : SpillSet)
    (hadded : ∃ id, source[found.1.get hsome] = .Var id ∧ spills = insert id state.spills) :
    State.TargetAvailable (target := target)
      { state with spills, dropped := state.dropped.set (found.1.get hsome) 1 } ∧
    DropCompatible { state with spills, dropped := state.dropped.set (found.1.get hsome) 1 }
      mapping (droppedNow.set (found.1.get hsome) 1) := by
  obtain ⟨id, hvalue, rfl⟩ := hadded
  constructor
  · refine targetAvailable_drop state mapping droppedNow havailable hcompatible _ _
      (hselected.get hsome).2.2 _ ?_ ?_
    · intro value h
      cases value <;> simp_all [SpillSet.is_spilled]
    · intro _
      simp [hvalue, SpillSet.is_spilled]
  · exact dropCompatible_set state mapping droppedNow hcompatible _ _

theorem resolve_targetAvailable_triple (init : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) :
    ⦃⌜init.TargetAvailable ∧ init.RetainedUndropped mapping⌝⦄ resolve init mapping blocked current
    ⦃post⟨fun result => ⌜result.2.TargetAvailable⌝, fun _ => ⌜True⌝⟩⦄ := by
  unfold resolve
  mvcgen
  case inv1 =>
    exact post⟨fun (_, candidates) => ⌜RetainedCandidates mapping candidates⌝, fun _ => ⌜True⌝⟩
  case inv2 =>
    -- Keep the property for both the current state and an early return after partial progress.
    exact post⟨fun (_, s) => ⌜s.2.1.TargetAvailable ∧ DropCompatible s.2.1 mapping s.2.2 ∧
      ∀ r, s.1 = some r → r.2.TargetAvailable⌝, fun _ => ⌜True⌝⟩
  case inv3 =>
    rename_i candidates _ _ _ _ _ s _ state droppedNow _ _
    exact post⟨fun (_, found) => ⌜Selected state mapping droppedNow candidates found⌝,
      fun _ => ⌜True⌝⟩
  all_goals dsimp at *
  all_goals try simp_all
  all_goals first
    | assumption
    | exact RetainedCandidates.append (by assumption) (by assumption)
    | exact RetainedCandidates.start _
    | exact Selected.start _ _ _ _
    | exact Selected.select _ _ _ _ _ (by simp) (by assumption) (by assumption) _
    | exact Option.isSome_iff_ne_none.mpr (by assumption)
    | (apply_assumption; simp)
    | exact dropCompatible_start _ _ (by tauto)
    | tauto
    | skip
  case vc15.step.post.success.isFalse.post.success.isTrue.pre =>
    rename_i hinv hne hselected hfour
    apply classify_four
    have hclass := (hselected.get (Option.isSome_iff_ne_none.mpr hne)).2.2
    convert hclass using 2
    exact congrArg some hfour.symm
  case vc16.step.post.success.isFalse.post.success.isTrue.post.success =>
    rename_i hinv hne hselected hfour hadded
    exact selected_spill_drop_preserves _ _ _ _ _ hselected _ hinv.1 hinv.2.1 _ hadded
  case vc17.step.post.success.isFalse.post.success.isFalse =>
    rename_i hinv hne hselected hfour
    exact selected_drop_preserves _ _ _ _ _ hselected _ hinv.1 hinv.2.1 hfour

end Shuffler.Planner
