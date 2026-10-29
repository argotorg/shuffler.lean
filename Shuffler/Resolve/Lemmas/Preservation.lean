module

public import Shuffler.Resolve.Defs
public import Shuffler.Resolve.Properties
public import Std.WP.Monad.Instances
public import Std.WP.Triple.Basic
import Shuffler.Resolve.Lemmas
import Shuffler.Resolve.Lemmas.PreservationHelpers
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP

set_option experimental.vcgen true

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
    ⦃init.TargetAvailable ∧ init.RetainedUndropped mapping⦄ resolve init mapping blocked current
    ⦃fun result => result.2.TargetAvailable; fun _ => True⦄ := by
  refine ⟨fun hinit => ?_⟩
  unfold resolve
  dsimp only
  refine (Triple.bind _ _ _ (resolve_candidates_triple mapping blocked current)
    fun candidates => ?_).le_wp trivial
  vcgen
  case inv1 =>
    -- Keep the property for both the current state and an early return after partial progress.
    exact fun _ _ s => s.2.1.TargetAvailable ∧ DropCompatible s.2.1 mapping s.2.2 ∧
      ∀ r, s.1 = some r → r.2.TargetAvailable
  case inv2 =>
    rename_i state droppedNow _
    exact fun _ _ found => Selected state mapping droppedNow candidates found
  all_goals dsimp at *
  all_goals try simp_all
  all_goals try first
    | exact dropCompatible_start _ _ hinit.2
    | exact Selected.start _ _ _ _
    | exact Selected.select _ _ _ _ _ (by simp) (by assumption) (by assumption) _
    | exact Selected.four (by assumption) _ rfl
    | exact Option.isSome_iff_ne_none.mpr (by assumption)
    | exact RetainedCandidates.current (by assumption)
  case vc8 =>
    rename_i hinv hselected _ _ hadded
    exact selected_spill_drop_preserves _ _ _ _ _ hselected _ hinv.1 hinv.2.1 _ hadded
  case vc9 =>
    rename_i hinv hselected _ hfour
    exact selected_drop_preserves _ _ _ _ _ hselected _ hinv.1 hinv.2.1 hfour

end Shuffler.Planner
