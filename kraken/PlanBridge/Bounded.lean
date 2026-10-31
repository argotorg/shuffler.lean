import Shuffler.Emission.Run.Lemmas.Execution
import Std.WP.Triple.SpecLemmas

/-!
The blocked offset of a PR31 `Emission.run` result lies below the height of its stack
(`run_bounded`). The flat `resolve` starts at `blockedOffset + 1`, so the bridge needs the bound.
-/

open Std.WP
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

namespace Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}

def Result.Bounded (result : Result source target spills) : Prop :=
  ∀ b, result.blocked = some b → b.offset < result.state.stack.length

theorem permute_bounded (state : State source target spills) (p : Permute.Permutation state.stack)
    {result} (h : Permute.permute state p = .ok result) : result.Bounded := by
  obtain ⟨q, hq, _⟩ := Permute.normalize_spec state.stack p
  rw [Permute.permute_eq_normalize, hq, except_ok_bind] at h
  by_cases hne : 0 < state.stack.length
  · rw [dite_eq_left hne] at h
    obtain ⟨r, hr, hs⟩ := Permute.go_spec state q hne
    rw [hr] at h
    cases h
    intro b hb
    obtain ⟨i, hi, _⟩ := hs.blocked b hb
    rw [hs.length, hi]
    exact i.isLt
  · rw [dite_eq_right hne] at h
    cases h
    simp [Result.Bounded]

@[local spec high] theorem removeSurplus_bounded_triple (initial : State source target spills) :
    ⦃True⦄ removeSurplus initial ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
  vcgen [removeSurplus, State.pop, State.swapWith, State.swapDestinations,
    State.blockSwapUnreachable, State.block, index, slotAt, requires]
  case inv1 => exact fun _ _ out => ∀ result, out.1 = some result → result.Bounded
  case inv2 => exact fun _ _ _ => True
  case inv3 => exact fun _ _ _ => True
  all_goals dsimp only at *
  all_goals simp_all [Result.Bounded]


@[local spec high] theorem permute_bounded_triple (state : State source target spills)
    (p : Permute.Permutation state.stack) :
    ⦃True⦄ Permute.permute state p ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
  cases he : Permute.permute state p with
  | error err => exact ⟨fun _ => trivial⟩
  | ok result => exact ⟨fun _ => permute_bounded state p he⟩

@[local spec high] theorem permuteAtLowestHeight_bounded_triple (state : State source target spills) :
    ⦃True⦄ PermuteAtLowestHeight.permuteAtLowestHeight state
    ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
  vcgen [PermuteAtLowestHeight.permuteAtLowestHeight, requires, index]
  case inv1 => exact fun _ _ _ => True
  case inv2 => exact fun _ _ _ => True
  all_goals simp_all

@[local spec high] theorem produce_bounded_triple (state : State source target spills)
    (offset : Fin target.length) :
    ⦃True⦄ state.produce offset
    ⦃fun result => result.Bounded ∧
      (result.blocked = none → result.state.pending_generations = state.pending_generations - 1);
      (fun _ => True)⦄ := by
  vcgen [State.produce, State.push, State.dup, State.blockDupUnreachable, State.block,
    requires, index]
  all_goals simp_all [Result.Bounded]

@[local spec high] theorem generate_bounded_triple (state : State source target spills)
    (offset : ℕ) :
    ⦃True⦄ state.generate offset
    ⦃fun result => result.Bounded ∧
      (result.blocked = none → result.state.pending_generations = state.pending_generations - 1);
      (fun _ => True)⦄ := by
  vcgen [State.generate, State.swapDestinations, State.swapWith, index, slotAt, requires]
  all_goals simp_all [Result.Bounded]

@[local spec high] theorem generate_attach_bounded_triple (state : State source target spills)
    (offset : ℕ) :
    ⦃True⦄ (state.generate offset).attach
    ⦃fun result => result.val.Bounded ∧
      (result.val.blocked = none →
        result.val.state.pending_generations = state.pending_generations - 1);
      (fun _ => True)⦄ := by
  have h := (generate_bounded_triple state offset).le_wp trivial
  cases he : state.generate offset with
  | error err =>
    simp only [Except.attach]
    exact ⟨fun _ => trivial⟩
  | ok result =>
    rw [he] at h
    exact ⟨fun _ => h⟩

@[local spec high] theorem buildBottomUp_loop_bounded_triple (cursor : ℕ)
    (state : State source target spills) :
    ⦃True⦄ buildBottomUp.loop cursor state ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
  rw [buildBottomUp.loop.eq_def]
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    exact ⟨fun _ b hb => nomatch hb⟩
  simp only [hdone, ↓reduceIte]
  have advance (next : State source target spills) :
      ⦃True⦄ buildBottomUp.loop (cursor + 1) next
      ⦃fun result => result.Bounded; (fun _ => True)⦄ :=
    buildBottomUp_loop_bounded_triple (cursor + 1) next
  have retry (next : State source target spills) :
      ⦃next.pending_generations < state.pending_generations⦄ buildBottomUp.loop cursor next
      ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
    constructor
    intro hlt
    exact (buildBottomUp_loop_bounded_triple cursor next).le_wp trivial
  vcgen [State.swapDestinations, State.swapWith, State.blockDupUnreachable,
    State.blockSwapUnreachable, State.block, index, slotAt, requires, advance, retry]
  case inv1 | inv4 =>
    exact fun _ _ out => ∀ result, out.1 = some result → result.Bounded
  case inv2 | inv3 | inv5 | inv6 => exact fun _ _ _ => True
  all_goals simp_all [Result.Bounded]
  all_goals omega
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

@[local spec high] theorem buildBottomUp_bounded_triple (state : State source target spills)
    (hvalid : state.Valid) :
    ⦃True⦄ buildBottomUp state hvalid ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
  vcgen [buildBottomUp, requires]

theorem run_bounded_triple (source target : Stack)
    (mapping : Mapping source.length target.length) (spills : SpillSet) :
    ⦃True⦄ run source target mapping spills ⦃fun result => result.Bounded; (fun _ => True)⦄ := by
  vcgen [run, requires]

theorem run_bounded {source target : Stack} {mapping : Mapping source.length target.length}
    {spills : SpillSet} {result} (h : run source target mapping spills = .ok result) :
    result.Bounded := by
  have h' := (run_bounded_triple source target mapping spills).le_wp trivial
  rw [h] at h'
  exact h'

end Shuffler.Emission
