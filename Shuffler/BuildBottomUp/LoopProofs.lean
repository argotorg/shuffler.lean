import Experiments.BuildBottomUp.CheckedProofs
import Experiments.BuildBottomUp.ScanProofs

open Std.Internal.Do

set_option mvcgen.warning false

namespace BuildBottomUpExperiments.Checked

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def StepPost (cursor : ℕ) (state : State source target spills) :
    ForInStep (Frame source target spills) → Prop
  | .done out => Spec (finishLoop out) (fun _ => True)
  | .yield out => out.1 = none ∧ Invariant out.2.2 out.2.1 ∧
      Prod.Lex Nat.lt Nat.lt (target.length - out.2.2, out.2.1.pending_generations)
        (target.length - cursor, state.pending_generations)

theorem StepPost.advance {state next : State source target spills}
    (hc : cursor < target.length) (inv : Invariant (cursor + 1) next) :
    StepPost cursor state (.yield (none, next, cursor + 1)) := by
  refine ⟨rfl, inv, ?_⟩
  exact Prod.Lex.left _ _ (show target.length - (cursor + 1) < target.length - cursor by omega)

theorem StepPost.retry {state next : State source target spills}
    (inv : Invariant cursor next) (h : next.pending_generations < state.pending_generations) :
    StepPost cursor state (.yield (none, next, cursor)) :=
  ⟨rfl, inv, Prod.Lex.right _ h⟩

-- Verify the common placement tail of the actual loop body.
macro "finish_checked " c:term ", " st:term ", " hp:term ", " hn:term ", " hc:term : tactic => `(tactic| (
  try rw [ensure_of_true _ $hn]
  try simp only [not_false_eq_true, ensure_of_true True True.intro, except_ok_bind, except_error_bind, pure_bind, bind_assoc]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    let pos : Fin ($st).stack.length := ⟨$c, ($hp).in_bounds⟩
    have hbelow := Stack.belowOfNotTop ($st).stack pos hnotTop
    by_cases hr : isSwapReachable $st $c
    · try dsimp +zetaDelta only at hr
      try simp +zetaDelta only [hr, not_true_eq_false, ↓reduceIte]
      simp_action
      apply (($hp).swap_final hbelow hr $hn).bind
      intro final hinv
      exact StepPost.advance $hc hinv
    · try dsimp +zetaDelta only at hr
      simp +zetaDelta only [hr, not_false_eq_true, ↓reduceIte]
      exact True.intro
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact StepPost.advance $hc (($hp).finish_at_top (not_not.mp hnotTop))))

theorem loop_step_spec (cursor : ℕ) (state : State source target spills)
    (inv : Invariant cursor state) :
    Spec ((loopStep (loopParts source target spills).val) () (none, state, cursor)) (StepPost cursor state) := by
  dsimp only [loopStep, loopParts]
  simp_action
  by_cases hc : cursor < target.length
  · simp only [hc, ↓reduceIte]
    by_cases hskip : cursor < state.stack.length ∧ state.isFinal cursor
    · simp only [hskip]
      exact StepPost.advance hc (inv.advance hskip.2)
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
          simp [liftResult, Except.mapError, Spec]
        | ok result =>
          cases result
          simp [liftResult, Except.mapError, except_ok_bind,
            Spec, StepPost, finishLoop, pure, Except.pure]
      · simp only [hz, ↓reduceIte]
        simp_action
        apply ((spec_iff_triple _ _).mpr (urgentScan_triple cursor state)).bind
        intro urgent hu
        split
        · rename_i hurg
          obtain ⟨hlt, hnone⟩ := hu (urgent.get hurg.1) (Option.some_get hurg.1).symm
          let u : Fin target.length := ⟨urgent.get hurg.1, hlt⟩
          have hb : state.mapping.symm u = none := by
            simpa [positionOf, hlt, u] using hnone
          simp_action
          apply (generate_contract state u hb (inv.available u)).bind
          intro next hgen
          exact StepPost.retry (hgen.invariant inv) (hgen.decreases inv)
        · split
          · rename_i htop
            let top : Fin target.length := ⟨state.stack.length, htop.2.2.1⟩
            have hb : state.mapping.symm top = none := by
              simpa [positionOf, top, top.isLt] using htop.2.2.2.1
            simp_action
            apply (generate_contract state top hb (inv.available top)).bind
            intro next hgen
            exact StepPost.retry (hgen.invariant inv) (hgen.decreases inv)
          · have hposition : positionOf state cursor = (state.mapping.symm dest).map Fin.val := by
              simp [positionOf, hc, dest]
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
                exact StepPost.advance hc (hp.toInvariant.advance hf)
              · simp only [hf, ↓reduceIte]
                finish_checked cursor, next, hp, hf, hc
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
                apply StepPost.advance hc
                apply hi.advance
                have hd : (state.mapping.swapDestinations current carrier).symm dest = some current := by
                  simp [hb]
                exact (State.isFinal_of_bound_iff
                  { state with mapping := state.mapping.swapDestinations current carrier }
                  dest current hd).mpr rfl
              · simp_action
                have hscan := (spec_iff_triple _ _).mpr (copyScan_triple state carrier.val carrier.isLt carrier.val
                  ⟨carrier, rfl, rfl, state.boundNotFinal_of_not_final dest carrier hb hnfinal⟩)
                simp only [slotAt_index state.stack carrier, except_ok_bind] at hscan
                apply hscan.bind
                intro selected hselected
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
                by_cases hplaced : pos.val = cursor
                · simp only [hplaced, ↓reduceIte]
                  exact StepPost.advance hc (hi.advance
                    ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced))
                · simp only [hplaced, ↓reduceIte]
                  by_cases hnotTop : pos.val ≠ retag.stack.length - 1
                  · dsimp +zetaDelta only at hnotTop
                    simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
                    have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
                    by_cases hr : isSwapReachable retag pos.val
                    · dsimp +zetaDelta only at hr
                      simp only [hr, not_true_eq_false, ↓reduceIte]
                      simp_action
                      apply (hi.swap_bound (dest := dest) pos hd hbelow hr hplaced).bind
                      intro next hp
                      finish_checked cursor, next, hp.1, hp.2, hc
                    · dsimp +zetaDelta only at hr
                      simp only [hr, not_false_eq_true, ↓reduceIte]
                      exact True.intro
                  · dsimp +zetaDelta only at hnotTop
                    simp only [ne_eq, hnotTop, ↓reduceIte]
                    have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
                    finish_checked cursor, retag, hp.1, hp.2, hc
  · simp only [hc, ↓reduceIte]
    change Spec (finishLoop (none, state, cursor)) (fun _ => True)
    rw [finishLoop, ensure_of_true _ (inv.complete_size (by omega))]
    trivial

def BodyPost (cursor : ℕ) (state : State source target spills)
    (step : ForInStep (ControlFrame source spills)) (next : State source target spills) : Prop :=
  StepPost cursor state (match step with
    | .done out => .done (out.1, next, out.2)
    | .yield out => .yield (out.1, next, out.2))

@[spec] theorem loop_body_triple (frame : ControlFrame source spills) (state : State source target spills)
    (hnone : frame.1 = none) (inv : Invariant frame.2 state) :
    ⦃fun s => s = state⦄ (loopParts source target spills).val () frame
    ⦃BodyPost frame.2 state; allowedErrors⦄ := by
  obtain ⟨result, cursor⟩ := frame
  dsimp at hnone
  subst result
  apply (action_triple_iff _ _ _).mpr
  have h := loop_step_spec cursor state inv
  unfold loopStep at h
  cases heq : ((loopParts source target spills).val () (none, cursor)).run state with
  | error err => cases err <;> simp_all [Spec]
  | ok result =>
    obtain ⟨step, next⟩ := result
    cases step <;> simpa [heq, Spec, BodyPost] using h

@[spec] theorem finishAction_triple (frame : ControlFrame source spills) :
    ⦃fun state : State source target spills => Spec (finishLoop (frame.1, state, frame.2)) (fun _ => True)⦄
      finishAction frame ⦃fun _ _ => True; allowedErrors⦄ := by
  vcgen [finishAction]
  by_contra hn
  simp_all [finishLoop, ensure, requires, Spec, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

private def LoopInvariant : RepeatInvariant (ControlFrame source spills) (ControlFrame source spills)
    (State source target spills → Prop)
  | .inl frame, state => frame.1 = none ∧ Invariant frame.2 state
  | .inr frame, state => Spec (finishLoop (frame.1, state, frame.2)) (fun _ => True)

theorem build_action_triple (cursor : ℕ) :
    ⦃Invariant cursor⦄ (do
      let frame ← forIn ({} : Lean.Loop) (none, cursor) (loopParts source target spills).val
      finishAction frame)
    ⦃fun (_ : Result source spills) (_ : State source target spills) => True; allowedErrors⦄ := by
  vcgen [loop_body_triple, finishAction_triple] invariants
  · LoopInvariant
  · RepeatVariant.ofMeasure (fun (frame : ControlFrame source spills) (state : State source target spills) =>
      (target.length - frame.2, state.pending_generations))
  all_goals try simp_all [LoopInvariant]
  case vc3 =>
    rename_i initial hinit frame measure before step after hm hp
    cases step with
    | done out => exact hp
    | yield out =>
      change out.1 = none ∧ Invariant out.2 after ∧ _ at hp
      simp only [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and, LoopInvariant]
      refine ⟨?_, hp.1, hp.2.1⟩
      rw [RepeatVariant.evalsBelow_ofMeasure_apply, RepeatVariant.evalsBelow_ofMeasure]
      rw [Lean.Order.ofProp_prop_eq]
      change Prod.Lex Nat.lt Nat.lt _ _
      rw [← hm.1]
      exact hp.2.2

end BuildBottomUpExperiments.Checked
