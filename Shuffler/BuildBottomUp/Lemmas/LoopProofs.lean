import Shuffler.BuildBottomUp.Lemmas.HelperProofs
import Shuffler.BuildBottomUp.Lemmas.ScanProofs
import Shuffler.Permute.Theorems

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Verify the common placement tail of the actual loop body.
macro "finish_checked " c:term ", " st:term ", " hp:term ", " hn:term ", " expected:term ", " advance:term : tactic => `(tactic| (
  try rw [ensure_of_true _ $hn]
  try simp only [not_false_eq_true, ensure_of_true True True.intro, except_ok_bind, except_error_bind, pure_bind, bind_assoc]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    let pos : Fin ($st).stack.length := ⟨$c, ($hp).in_bounds⟩
    try simp_action
    rw [isSwapReachable_index $st pos]
    simp only [except_ok_bind, decide_eq_true_eq]
    have hbelow := Stack.belowOfNotTop ($st).stack pos hnotTop
    by_cases hr : ($st).stack.isSwapReachable pos
    · try dsimp +zetaDelta only at hr
      try simp +zetaDelta only [hr, not_true_eq_false, ↓reduceIte]
      try simp_action
      apply (($hp).swap_final hbelow hr $hn).bind
      rintro final ⟨hinv, he⟩
      exact $advance _ hinv (he.trans $expected)
    · try dsimp +zetaDelta only at hr
      simp +zetaDelta only [hr, not_false_eq_true, ↓reduceIte]
      try simp_action
      rw [depthOf_index $st pos]
      simp only [except_ok_bind]
      exact True.intro
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop)) $expected))


theorem loop_spec (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    Spec (buildBottomUp.loop cursor state) (fun result => result.1.1 = state.expectedStack) := by
  rw [buildBottomUp.loop.eq_def]
  simp_action
  by_cases hc : cursor < target.length
  · have advance (next : State source target spills) (hi : Invariant (cursor + 1) next)
        (he : next.expectedStack = state.expectedStack) :
        Spec (buildBottomUp.loop (cursor + 1) next) (fun result => result.1.1 = state.expectedStack) :=
      (loop_spec (cursor + 1) next hi).mono (fun _ hr => hr.trans he)
    have retry (next : State source target spills) (hi : Invariant cursor next)
        (hlt : next.pending_generations < state.pending_generations)
        (he : next.expectedStack = state.expectedStack) :
        Spec (buildBottomUp.loop cursor next) (fun result => result.1.1 = state.expectedStack) :=
      (loop_spec cursor next hi).mono (fun _ hr => hr.trans he)
    simp only [hc, ↓reduceIte]
    by_cases hskip : cursor < state.stack.length ∧ state.isFinal cursor
    · simp only [hskip]
      exact advance _ (inv.advance hskip.2) rfl
    · simp only [hskip, ↓reduceIte]
      let dest : Fin target.length := ⟨cursor, hc⟩
      have hnfinal : ¬ state.isFinal cursor := by
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
        cases hperm : Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hp.1 hp.2) with
        | error err =>
          cases err
          simp [Except.mapError, Spec]
        | ok result =>
          obtain ⟨res, trace⟩ := result
          simp only [Except.mapError, except_ok_bind, Spec, pure, Except.pure]
          exact (Shuffler.Permute.permute_applies_permutation_of_ok _ _ _ hperm).trans
            (expectedStack_permutation state hp.1 hp.2)
      · simp only [hz, ↓reduceIte]
        rw [StateT.run_bind]
        have hscan := (action_triple_iff _ _ _).mp (urgentScan_triple cursor state)
        simp only [bind_pure] at hscan
        apply hscan.bind
        rintro ⟨urgent, next⟩ ⟨hu, hnext⟩
        dsimp only at hu hnext ⊢
        subst next
        split
        · rename_i hurg
          obtain ⟨hlt, hnone⟩ := hu (urgent.get hurg.1) (Option.some_get hurg.1).symm
          let u : Fin target.length := ⟨urgent.get hurg.1, hlt⟩
          have hb : state.mapping.symm u = none := by
            simpa [State.positionOf, hlt, u] using hnone
          simp_action
          apply (generate_contract state u hb (inv.available u)).bind
          intro next hgen
          exact retry _ (hgen.invariant inv) (hgen.decreases inv) hgen.expected
        · split
          · rename_i htop
            let top : Fin target.length := ⟨state.stack.length, htop.2.2.1⟩
            have hb : state.mapping.symm top = none := by
              simpa [State.positionOf, top, top.isLt] using htop.2.2.2.1
            simp_action
            apply (generate_contract state top hb (inv.available top)).bind
            intro next hgen
            exact retry _ (hgen.invariant inv) (hgen.decreases inv) hgen.expected
          · have hposition : state.positionOf cursor = (state.mapping.symm dest).map Fin.val := by
              simp [State.positionOf, hc, dest]
            rw [hposition]
            cases hb : state.mapping.symm dest with
            | none =>
              simp only [Option.map_none]
              simp_action
              apply (generate_contract state dest hb (inv.available dest)).bind
              intro next hgen
              have hp := hgen.placement inv
              by_cases hf : next.isFinal cursor
              · simp only [hf, ↓reduceIte]
                exact advance _ (hp.toInvariant.advance hf) hgen.expected
              · simp only [hf, ↓reduceIte]
                finish_checked cursor, next, hp, hf, hgen.expected, advance
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
                apply advance _
                · apply hi.advance
                  have hd : (state.mapping.swapDestinations current carrier).symm dest = some current := by
                    simp [hb]
                  exact (State.isFinal_of_bound_iff
                    { state with mapping := state.mapping.swapDestinations current carrier }
                    dest current hd).mpr rfl
                · exact (expectedStack_retag state current carrier hequal).symm
              · rw [depthOf_index state carrier]
                simp only [except_ok_bind]
                have hscan := (action_triple_iff _ _ _).mp (copyScan_triple state carrier carrier.val
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
                have hd : retag.mapping.symm dest = some pos := by simp [retag, hb]
                have he : retag.expectedStack = state.expectedStack :=
                  (expectedStack_retag state pos carrier hequal).symm
                by_cases hplaced : pos.val = cursor
                · simp only [hplaced, ↓reduceIte]
                  exact advance _ (hi.advance
                    ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced)) he
                · simp only [hplaced, ↓reduceIte]
                  by_cases hnotTop : pos.val ≠ retag.stack.length - 1
                  · dsimp +zetaDelta only at hnotTop
                    simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
                    rw [isSwapReachable_index retag pos]
                    simp only [except_ok_bind, decide_eq_true_eq]
                    have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
                    by_cases hr : retag.stack.isSwapReachable pos
                    · dsimp +zetaDelta only at hr
                      simp +zetaDelta only [hr, not_true_eq_false, ↓reduceIte]
                      apply (hi.swap_bound (dest := dest) pos hd hbelow hr hplaced).bind
                      rintro next ⟨hp, he'⟩
                      finish_checked cursor, next, hp.1, hp.2, he'.trans he, advance
                    · dsimp +zetaDelta only at hr
                      simp +zetaDelta only [hr, not_false_eq_true, ↓reduceIte]
                      rw [depthOf_index retag pos]
                      simp only [except_ok_bind]
                      exact True.intro
                  · dsimp +zetaDelta only at hnotTop
                    simp only [ne_eq, hnotTop, ↓reduceIte]
                    have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
                    finish_checked cursor, retag, hp.1, hp.2, he, advance
  · simp only [hc, ↓reduceIte]
    rw [ensure_of_true _ (inv.complete_size (by omega))]
    exact inv.expected_done (by omega)
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

theorem buildBottomUp_spec (initial : State source target spills) (h : initial.Valid) :
    Spec (buildBottomUp initial) (fun result => result.1 = initial.expectedStack) := by
  unfold buildBottomUp
  rw [StateT.run'_eq]
  exact (loop_spec 0 initial (Invariant.initial h)).bind (fun _ he => he)

end Shuffler.BuildBottomUp
