import Shuffler.BuildBottomUp.Optimality.Lemmas.ActionCounts
import Shuffler.BuildBottomUp.Optimality.Lemmas.PermuteBound
import Shuffler.BuildBottomUp.Lemmas.LoopProofs

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

macro "finish_extends " c:term ", " st:term ", " hp:term ", " hn:term ", " extension:term ", " advance:term : tactic => `(tactic| (
  try rw [index_eq (⟨$c, ($hp).in_bounds⟩ : Fin ($st).stack.length)]
  try simp only [except_ok_bind]
  try rw [requires_of_true (¬ ($st).isFinal ⟨$c, ($hp).in_bounds⟩)
    ((($st).isFinal_iff ⟨$c, ($hp).in_bounds⟩).not.mpr $hn)]
  try simp only [not_false_eq_true, requires_of_true True True.intro, except_ok_bind,
    except_error_bind, pure_bind, bind_assoc]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    have hbelow := Stack.belowOfNotTop ($st).stack ⟨$c, ($hp).in_bounds⟩ hnotTop
    by_cases hr : ($st).isSwapReachable ⟨$c, ($hp).in_bounds⟩
    · rw [ite_eq_right (not_not_intro hr)]
      try simp_loop
      apply (($hp).swap_final hbelow hr $hn).with_eq.bind
      rintro final ⟨⟨hinv, _⟩, hrun⟩
      exact $advance _ hinv (($extension).trans (swap_counts $st final $c hrun).extension)
    · rw [ite_eq_left hr]
      exact True.intro
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop)) $extension))

-- Every loop step appends operations to the current trace.
theorem loop_extends (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) :
    Spec (buildBottomUp.loop cursor state) (fun result => Extends state.trace result.2) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    exact Extends.refl _
  have hc : cursor < target.length := Nat.lt_of_not_ge hdone
  have advance (next : State source target spills) (hi : next.invariant (cursor + 1))
      (he : Extends state.trace next.trace) :
      Spec (buildBottomUp.loop (cursor + 1) next) (fun result => Extends state.trace result.2) :=
    (loop_extends (cursor + 1) next hi).mono fun _ hx => he.trans hx
  have retry (next : State source target spills) (hi : next.invariant cursor)
      (hlt : next.pending_generations < state.pending_generations)
      (he : Extends state.trace next.trace) :
      Spec (buildBottomUp.loop cursor next) (fun result => Extends state.trace result.2) :=
    (loop_extends cursor next hi).mono fun _ hx => he.trans hx
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact advance _ (inv.advance hfinal) (Extends.refl _)
  let dest : Fin target.length := ⟨cursor, hc⟩
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  by_cases hz : state.pending_generations = 0
  · have ht : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
    have hs := inv.size
    have hp := state.mapping.complete_of_target_total (by omega) ht
    simp only [hz, ↓reduceIte, requires_of_true _ hp.1, except_ok_bind]
    rw [requires_of_true (∀ i, (state.destinationOf i).isSome) hp.2, except_ok_bind]
    cases hperm : Shuffler.Permute.permute spills state.stack
        (state.mapping.toPermutation hp.1 hp.2) with
    | error err =>
      cases err
      simp [Except.mapError, Spec]
    | ok result =>
      obtain ⟨res, trace⟩ := result
      simp only [Except.mapError, except_ok_bind, Spec, pure, Except.pure]
      exact ⟨trace, permute_noPop spills state.stack _ hperm, rfl⟩
  simp only [hz, ↓reduceIte]
  have hscan := (spec_iff_triple _ _).mpr (urgentScan_triple cursor state)
  simp only [bind_pure] at hscan
  apply hscan.bind
  intro urgent hu
  by_cases hurg : urgent.isSome ∧ urgent ≠ some cursor ∧ state.stack.length - cursor < MAX_SWAP_DEPTH
  · rw [dite_eq_left hurg]
    obtain ⟨hlt, hnone⟩ := hu (urgent.get hurg.1) (Option.some_get hurg.1).symm
    let u : Fin target.length := ⟨urgent.get hurg.1, hlt⟩
    have hb : state.mapping.symm u = none := by
      simpa [State.positionOf, hlt, u] using hnone
    apply (generate_contract state u hb (inv.available u)).with_eq.attach.bind
    intro next ⟨hgen, hrun⟩
    exact retry _ (hgen.invariant inv) (hgen.decreases inv)
      (generate_counts state _ _ hrun).extension
  rw [dite_eq_right hurg]
  apply Spec.ite_index (fun hA => hA.2.2)
  · intro _ hB
    let top : Fin target.length := ⟨state.stack.length, by omega⟩
    have hb : state.mapping.symm top = none := by
      simpa [State.positionOf, top] using hB.1
    apply (generate_contract state top hb (inv.available top)).with_eq.attach.bind
    intro next ⟨hgen, hrun⟩
    exact retry _ (hgen.invariant inv) (hgen.decreases inv)
      (generate_counts state _ _ hrun).extension
  rw [index_eq dest, except_ok_bind]
  rcases Option.eq_none_or_eq_some (state.positionOf dest) with hpos | ⟨carrier, hpos⟩
  · simp only [hpos]
    have hb : state.mapping.symm dest = none := hpos
    apply (generate_contract state dest hb (inv.available dest)).with_eq.bind
    intro next ⟨hgen, hrun⟩
    have hcounts := generate_counts state next dest.val hrun
    have hp := hgen.placement inv
    let current : Fin next.stack.length := ⟨cursor, hp.in_bounds⟩
    rw [index_eq current, except_ok_bind]
    by_cases hf : ∃ h, next.isFinal ⟨cursor, h⟩
    · rw [ite_eq_left ((next.isFinal_iff current).mpr hf)]
      exact advance _ (hp.toInvariant.advance hf) hcounts.extension
    · rw [ite_eq_right ((next.isFinal_iff current).not.mpr hf)]
      finish_extends cursor, next, hp, hf, hcounts.extension, advance
  · simp only [hpos]
    have hb : state.mapping.symm dest = some carrier := hpos
    have hge := inv.processed.bound_ge dest carrier hb le_rfl
    have hcurrent : cursor < state.stack.length := lt_of_le_of_lt hge carrier.isLt
    let current : Fin state.stack.length := ⟨cursor, hcurrent⟩
    rw [requires_of_true _ hge]
    simp only [except_ok_bind]
    rw [slotAt_index state.stack current, slotAt_index state.stack carrier]
    simp only [except_ok_bind]
    by_cases hequal : state.stack[current] = state.stack[carrier]
    · rw [ite_eq_left hequal, requires_of_true _ hequal]
      simp only [except_ok_bind]
      rw [swapDestinations_result state current carrier]
      simp only [except_ok_bind]
      have hi := inv.retag current carrier (by rfl) hge
      apply advance _
      · apply hi.advance
        have hd : (state.mapping.swapDestinations current carrier).symm dest = some current := by
          simp [hb]
        exact (State.isFinal_of_bound_iff
          { state with mapping := state.mapping.swapDestinations current carrier }
          dest current hd).mpr rfl
      · exact Extends.refl _
    rw [ite_eq_right hequal, index_eq carrier]
    simp only [except_ok_bind]
    have hscan := (spec_iff_triple _ _).mpr (copyScan_triple state carrier carrier.val
      ⟨carrier, rfl, rfl, state.boundNotFinal_of_not_final dest carrier hb hnfinal⟩)
    simp only [except_ok_bind, bind_pure, slotAt_index state.stack carrier] at hscan
    apply hscan.bind
    intro selected hselected
    obtain ⟨pos, rfl, hequal, hmovable⟩ := hselected
    rw [slotAt_index state.stack pos]
    simp only [except_ok_bind]
    rw [requires_of_true _ hequal]
    simp only [except_ok_bind]
    rw [swapDestinations_result state pos carrier]
    simp only [except_ok_bind]
    let retag := { state with mapping := state.mapping.swapDestinations pos carrier }
    have hi : retag.invariant cursor := inv.retag pos carrier
      (inv.not_final_ge pos hmovable) hge
    have hd : retag.mapping.symm dest = some pos := by simp [retag, hb]
    by_cases hplaced : pos.val = cursor
    · simp only [hplaced, ↓reduceIte]
      exact advance _ (hi.advance
        ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced)) (Extends.refl _)
    simp only [hplaced, ↓reduceIte]
    by_cases hnotTop : pos.val ≠ retag.stack.length - 1
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
      rw [index_eq (size := retag.stack.length) pos]
      simp only [except_ok_bind]
      have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
      by_cases hr : retag.isSwapReachable pos
      · rw [ite_eq_right (not_not_intro hr)]
        apply (hi.swap_bound (dest := dest) pos hd hbelow hr hplaced).with_eq.bind
        rintro next ⟨⟨hp, _⟩, hrun⟩
        finish_extends cursor, next, hp.1, hp.2, (swap_counts retag next pos.val hrun).extension, advance
      · rw [ite_eq_left hr]
        exact True.intro
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, ↓reduceIte]
      have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
      finish_extends cursor, retag, hp.1, hp.2, (Extends.refl _), advance
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

-- This identifies the actual emitted suffix, even after an earlier POP.
theorem buildBottomUp_extends (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result,trace⟩) : Extends initial.trace trace := by
  have hs := loop_extends 0 initial (State.invariant.initial h)
  rw [loop_eq_of_ok hrun] at hs
  exact hs

end Shuffler.Optimality.BBU
