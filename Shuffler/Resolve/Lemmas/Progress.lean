module

public import Shuffler.Resolve.Lemmas.PreservationHelpers
public import Std.WP.Monad.Instances
public import Std.WP.Triple.Basic
import Mathlib.Data.Fintype.Card
import Shuffler.Resolve.Lemmas
import Std.WP.Triple.SpecLemmas

@[expose] public section

open Std.WP

set_option experimental.vcgen true

namespace Shuffler.Planner

variable {source target : Stack}

theorem State.droppedCount_le (state : State source target) :
    state.droppedCount ≤ source.length := by
  unfold State.droppedCount
  calc
    _ ≤ (Finset.univ : Finset (Fin source.length)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = source.length := by simp

theorem droppedCount_set_one (state : State source target) (i : Fin source.length)
    (hi : state.dropped[i] = 0) :
    ({ state with dropped := state.dropped.set i 1 } : State source target).droppedCount = state.droppedCount + 1 := by
  unfold State.droppedCount
  have hset : (Finset.univ.filter fun j : Fin source.length =>
      (state.dropped.set i 1)[j] ≠ 0) =
      insert i (Finset.univ.filter fun j : Fin source.length => state.dropped[j] ≠ 0) := by
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Vector.getElem_set, hji, Fin.val_ne_of_ne (Ne.symm hji)]
  rw [hset, Finset.card_insert_of_notMem]
  simpa using hi

theorem progress_commit (initial state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (hcompatible : DropCompatible state mapping droppedNow) (offset : Fin source.length)
    (hretained : (mapping.destinationOf offset).isSome) (hzero : droppedNow[offset] = 0)
    (k : ℕ) (hcount : state.droppedCount = initial.droppedCount + k) (spills : SpillSet) :
    DropCompatible { state with spills, dropped := state.dropped.set offset 1 }
      mapping (droppedNow.set offset 1) ∧
    ({ state with spills, dropped := state.dropped.set offset 1 } : State source target).droppedCount =
      initial.droppedCount + (k + 1) := by
  refine ⟨dropCompatible_set _ _ _ hcompatible _ _, ?_⟩
  have hz := hcompatible offset hretained hzero
  have hstep := droppedCount_set_one ({ state with spills } : State source target) offset hz
  change ({ state with spills, dropped := state.dropped.set offset 1 } : State source target).droppedCount =
    state.droppedCount + 1 at hstep
  rw [hstep, hcount, Nat.add_assoc]

private theorem progress_none {ret : Option (Bool × State source target)}
    (hfalse : ∀ state, ret ≠ some (false, state))
    (htrue : ∀ state, ret ≠ some (true, state)) : ret = none := by
  cases ret with
  | none => rfl
  | some r => cases r with | mk flag state => cases flag <;> simp_all

@[local spec] theorem progress_classify_spec (state : State source target)
    (mapping : Mapping source.length target.length) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length) :
    ⦃True⦄ classify state mapping droppedNow offset ⦃fun _ => True; fun _ => True⦄ :=
  ⟨fun _ => by cases classify state mapping droppedNow offset <;> trivial⟩

@[local spec] theorem progress_spill_spec (spills : SpillSet) (value : Value) :
    ⦃True⦄ spills.add value ⦃fun _ => True; fun _ => True⦄ :=
  ⟨fun _ => by cases spills.add value <;> trivial⟩

@[local spec] theorem progress_requires_spec (p : Prop) [Decidable p] (reason : String) :
    ⦃True⦄ requires p reason ⦃fun _ => True; fun _ => True⦄ :=
  ⟨fun _ => by cases requires p reason <;> trivial⟩

theorem resolve_progress_triple (initial : State source target)
    (mapping : Mapping source.length target.length) (blocked : Blocked)
    {currentSize : ℕ} (current : Mapping currentSize target.length) :
    ⦃initial.RetainedUndropped mapping⦄ resolve initial mapping blocked current
    ⦃fun res => res.1 = true → res.2.droppedCount = initial.droppedCount + blocked.excess;
      fun _ => True⦄ := by
  refine ⟨fun hretained => ?_⟩
  unfold resolve
  dsimp only
  refine (Triple.bind _ _ _ (resolve_candidates_triple mapping blocked current)
    fun candidates => ?_).le_wp trivial
  vcgen
  case inv1 =>
    exact fun pref suff b => DropCompatible b.2.1 mapping b.2.2 ∧
      (b.1 = none → b.2.1.droppedCount = initial.droppedCount + pref.length) ∧
      (∀ ret, b.1 = some ret → suff = [] ∧ ret.1 = false)
  case inv2 =>
    rename_i _ droppedNow _
    exact fun _ _ found => ∀ i, found.1 = some i →
      (Mapping.destinationOf mapping i).isSome ∧ droppedNow[i] = 0
  all_goals dsimp +zetaDelta at *
  all_goals simp_all
  all_goals try exact (show PLift _ from by assumption).down
  all_goals try exact dropCompatible_start _ _ (by assumption)
  all_goals
    rename_i hloop hselected _ _
    apply progress_commit
    · exact hloop.1
    · exact (hselected _ (Option.some_get _).symm).1
    · exact (hselected _ (Option.some_get _).symm).2
    · exact hloop.2.1 (progress_none hloop.2.2.1 hloop.2.2.2)

end Shuffler.Planner
