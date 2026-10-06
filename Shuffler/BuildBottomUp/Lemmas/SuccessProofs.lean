import Shuffler.BuildBottomUp.Lemmas.ReachScan
import Shuffler.Permute.Theorems

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem Invariant.permutation_reachable {state : State source target spills}
    (inv : Invariant cursor state) (hr : WithinReach cursor state)
    (hlen : state.stack.length = target.length) (hsource : ∀ i, (state.mapping i).isSome) :
    Shuffler.Permute.all_swaps_reachable (state.mapping.toPermutation hlen hsource) := by
  intro i hi
  have hge : cursor ≤ i.val := by
    by_contra hn
    let j : Fin target.length := Fin.cast hlen i
    have hf := inv.processed j (by change i.val < cursor; omega)
    have hb : state.mapping.symm j = some i :=
      state.boundOfVal j i (by
        unfold State.isFinal at hf
        rw [dite_eq_left j.isLt] at hf
        exact hf)
    have he := Mapping.toPermutation_apply state.mapping hlen hsource i
    rw [state.mapping.eq_some_iff.mp hb] at he
    have hpos : state.mapping.toPermutation hlen hsource i = i := by
      apply Fin.ext
      have he' := congrArg Fin.val (Option.some.inj he)
      exact he'
    simp [hpos] at hi
  have := hr.width
  dsimp [Fin.rev]
  omega

macro "finish_reachable " c:term ", " st:term ", " hp:term ", " hn:term ", " hr:term ", " advance:term : tactic => `(tactic| (
  try rw [ensure_of_true _ $hn]
  try simp only [not_false_eq_true, ensure_of_true True True.intro, except_ok_bind, except_error_bind, pure_bind, bind_assoc]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    let pos : Fin ($st).stack.length := ⟨$c, ($hp).in_bounds⟩
    try simp_action
    rw [isSwapReachable_index $st pos]
    have hreach := ($hr).swap_reachable pos (by rfl)
    simp only [hreach, decide_true, not_true_eq_false, ↓reduceIte, except_ok_bind]
    try simp_action
    have hbelow := Stack.belowOfNotTop ($st).stack pos hnotTop
    apply (($hp).swap_final_success $hr hbelow $hn).bind
    rintro next ⟨hi, hreach⟩
    exact $advance _ hi hreach
  · try dsimp +zetaDelta only at hnotTop
    simp only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop)) ($hr).advance))

theorem loop_success (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) (hr : WithinReach cursor state) :
    Success (buildBottomUp.loop cursor state) (fun _ => True) := by
  rw [buildBottomUp.loop.eq_def]
  simp_action
  by_cases hc : cursor < target.length
  · have advance (next : State source target spills) (hi : Invariant (cursor + 1) next)
        (hr : WithinReach (cursor + 1) next) :
        Success (buildBottomUp.loop (cursor + 1) next) (fun _ => True) :=
      loop_success (cursor + 1) next hi hr
    have retry (next : State source target spills) (hi : Invariant cursor next)
        (hr : WithinReach cursor next) (hlt : next.pending_generations < state.pending_generations) :
        Success (buildBottomUp.loop cursor next) (fun _ => True) :=
      loop_success cursor next hi hr
    simp only [hc, ↓reduceIte]
    by_cases hskip : cursor < state.stack.length ∧ state.isFinal cursor
    · simp only [hskip]
      exact advance _ (inv.advance hskip.2) hr.advance
    · simp only [hskip, ↓reduceIte]
      let dest : Fin target.length := ⟨cursor, hc⟩
      have hnfinal : ¬state.isFinal cursor := by
        intro hf
        exact hskip ⟨state.isFinal_lt dest hf, hf⟩
      by_cases hz : state.pending_generations = 0
      · have ht : ∀ j, (state.mapping.symm j).isSome :=
          (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
        have hs := inv.size
        have hp := state.mapping.complete_of_target_total (by omega) ht
        simp only [hz, ↓reduceIte, requires, dite_eq_left hp, pure_bind]
        split
        simp_action
        obtain ⟨res, trace, heq, _⟩ := Shuffler.Permute.permute_applies_permutation_reachable
          spills state.stack (state.mapping.toPermutation hp.1 hp.2)
          (inv.permutation_reachable hr hp.1 hp.2)
        simp only [heq, Except.mapError, except_ok_bind]
        exact ⟨_, rfl, trivial⟩
      · simp only [hz, ↓reduceIte]
        rw [StateT.run_bind]
        have hscan := Success.of_triple _ _ _ (urgentScan_success cursor state hr.copies)
        simp only [bind_pure] at hscan
        apply hscan.bind
        rintro ⟨urgent, next⟩ ⟨hu, hnext⟩
        dsimp only at hu hnext ⊢
        subst next
        split
        · rename_i hurg
          obtain ⟨hlt, hnone⟩ := hu.choice (urgent.get hurg.1) (Option.some_get hurg.1).symm
          let u : Fin target.length := ⟨urgent.get hurg.1, hlt⟩
          have hb : state.mapping.symm u = none := by
            simpa [State.positionOf, hlt, u] using hnone
          have hready : Ready state u := (hu.selected u.val (Option.some_get hurg.1).symm).ready
          simp_action
          apply (generate_reachable state u hb (inv.available u) hr
            (inv.processed.unbound_ge u hb) hready).bind
          rintro next ⟨hg, hcopies, _⟩
          apply retry _ (hg.invariant inv) ⟨?_, hcopies⟩ (hg.decreases inv)
          have := hg.size
          have := hurg.2.2
          have := inv.cursor_le_length hc
          omega
        · rename_i hnurg
          split
          · rename_i htop
            let top : Fin target.length := ⟨state.stack.length, htop.2.2.1⟩
            have hb : state.mapping.symm top = none := by
              simpa [State.positionOf, top, top.isLt] using htop.2.2.2.1
            have hn : urgent = none := Option.isNone_iff_eq_none.mp htop.1
            have hready : Ready state top :=
              (hn ▸ hu).ready_none inv.processed htop.2.2.2.2 top
            simp_action
            apply (generate_reachable state top hb (inv.available top) hr
              (by exact Nat.le_of_lt htop.2.1) hready).bind
            rintro next ⟨hg, hcopies, _⟩
            apply retry _ (hg.invariant inv) ⟨?_, hcopies⟩ (hg.decreases inv)
            have := hg.size
            have := htop.2.2.2.2
            have := inv.cursor_le_length hc
            omega
          · have hposition : state.positionOf cursor = (state.mapping.symm dest).map Fin.val := by
              simp [State.positionOf, hc, dest]
            rw [hposition]
            cases hb : state.mapping.symm dest with
            | none =>
              simp only [Option.map_none]
              simp_action
              apply (generate_reachable state dest hb (inv.available dest) hr le_rfl
                (hu.ready_cursor inv.processed hr hc hnurg)).bind
              rintro next ⟨hg, hcopies, hf⟩
              have hfinal := hf (inv.cursor_le_length hc)
              change next.isFinal cursor at hfinal
              simp only [hfinal, ↓reduceIte]
              apply advance _ ((hg.invariant inv).advance hfinal) ⟨?_, hcopies⟩
              have := hg.size
              have := hr.width
              have := inv.cursor_le_length hc
              omega
            | some carrier =>
              simp only [Option.map_some]
              simp_action
              have hge := inv.processed.bound_ge dest carrier hb le_rfl
              have hcurrent : cursor < state.stack.length := lt_of_le_of_lt hge carrier.isLt
              let current : Fin state.stack.length := ⟨cursor, hcurrent⟩
              rw [ensure_of_true _ hge]
              simp only [except_ok_bind]
              rw [slotAt_index state.stack current, slotAt_index state.stack carrier]
              simp_action
              split
              · rename_i hequal
                rw [ensure_of_true _ hequal]
                simp_action
                rw [swapDestinations_result state current carrier]
                have hi := inv.retag current carrier (by rfl) hge
                apply advance _ _ (hr.retag current carrier).advance
                apply hi.advance
                have hd : (state.mapping.swapDestinations current carrier).symm dest = some current := by
                  simp [hb]
                exact (State.isFinal_of_bound_iff
                  { state with mapping := state.mapping.swapDestinations current carrier }
                  dest current hd).mpr rfl
              · rw [depthOf_index state carrier]
                simp only [except_ok_bind]
                have hscan := Success.of_triple _ _ _ (copyScan_success state carrier carrier.val
                  ⟨carrier, rfl, rfl, state.boundNotFinal_of_not_final dest carrier hb hnfinal⟩)
                simp only [bind_pure, slotAt_index state.stack carrier] at hscan
                rw [StateT.run_bind]
                apply hscan.bind
                rintro ⟨selected, next⟩ ⟨hselected, hnext⟩
                dsimp only at hselected hnext ⊢
                subst next
                obtain ⟨pos, rfl, hequal, hmovable⟩ := hselected
                rw [slotAt_index state.stack pos]
                simp_action
                rw [ensure_of_true _ hequal]
                simp_action
                rw [swapDestinations_result state pos carrier]
                simp_action
                let retag := { state with mapping := state.mapping.swapDestinations pos carrier }
                have hi : Invariant cursor retag := inv.retag pos carrier
                  (inv.not_final_ge pos hmovable) hge
                have hrt : WithinReach cursor retag := hr.retag pos carrier
                have hd : retag.mapping.symm dest = some pos := by simp [retag, hb]
                by_cases hplaced : pos.val = cursor
                · simp only [hplaced, ↓reduceIte]
                  exact advance _ (hi.advance
                    ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced)) hrt.advance
                · simp only [hplaced, ↓reduceIte]
                  by_cases hnotTop : pos.val ≠ retag.stack.length - 1
                  · dsimp +zetaDelta only at hnotTop
                    simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
                    rw [isSwapReachable_index retag pos]
                    have hreach := hrt.swap_reachable pos (hi.processed.bound_ge dest pos hd le_rfl)
                    simp only [hreach, decide_true, not_true_eq_false, ↓reduceIte, except_ok_bind]
                    try simp_action
                    have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
                    apply (hi.swap_bound_success (dest := dest) hrt pos hd hbelow hplaced).bind
                    rintro next ⟨hp, hrn⟩
                    finish_reachable cursor, next, hp.1, hp.2, hrn, advance
                  · dsimp +zetaDelta only at hnotTop
                    simp only [ne_eq, hnotTop, ↓reduceIte]
                    have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
                    finish_reachable cursor, retag, hp.1, hp.2, hrt, advance
  · simp only [hc, ↓reduceIte]
    rw [ensure_of_true _ (inv.complete_size (by omega))]
    exact ⟨_, rfl, trivial⟩
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

theorem buildBottomUp_success (initial : State source target spills) (h : initial.Valid)
    (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    Success (buildBottomUp initial) (fun _ => True) := by
  unfold buildBottomUp
  rw [StateT.run'_eq]
  exact (loop_success 0 initial (Invariant.initial h) (WithinReach.initial h hsmall)).bind
    (fun result _ => ⟨result.1, rfl, trivial⟩)

-- The loop skips a final prefix without changing the state.
theorem loop_zero_eq_of_processed (state : State source target spills)
    (hp : Processed cursor state) :
    buildBottomUp.loop 0 state = buildBottomUp.loop cursor state := by
  induction cursor with
  | zero => rfl
  | succ cursor ih =>
    rw [ih (fun i hi => hp i (by omega))]
    by_cases hc : cursor < target.length
    · have hf := hp ⟨cursor, hc⟩ (by simp)
      have hs := state.isFinal_lt ⟨cursor, hc⟩ hf
      rw [buildBottomUp.loop.eq_def]
      simp only [Action.run_get, hc, ↓reduceIte, hs, hf, and_self]
      rfl
    · have hn : ¬cursor + 1 < target.length := by omega
      conv_lhs => rw [buildBottomUp.loop.eq_def]
      conv_rhs => rw [buildBottomUp.loop.eq_def]
      simp only [hc, hn, ↓reduceIte]

theorem buildBottomUp_success_of_processed (initial : State source target spills)
    (h : initial.Valid) (hp : Processed cursor initial) (hr : WithinReach cursor initial) :
    Success (buildBottomUp initial) (fun _ => True) := by
  unfold buildBottomUp
  rw [StateT.run'_eq]
  change Success ((fun result => result.1) <$> buildBottomUp.loop 0 initial) _
  rw [loop_zero_eq_of_processed initial hp]
  exact (loop_success cursor initial ⟨hp, h.size, h.pending, h.available⟩ hr).bind
    (fun result _ => ⟨result.1, rfl, trivial⟩)

end Shuffler.BuildBottomUp
