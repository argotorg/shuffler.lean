import Shuffler.BuildBottomUp.Lemmas.HelperProofs
import Shuffler.BuildBottomUp.Lemmas.ScanProofs
import Shuffler.Permute.Theorems

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Inline join points and reduce binds on known results.
macro "simp_loop" : tactic => `(tactic| simp only [bind_assoc, pure_bind, except_ok_bind, except_error_bind])

-- Verify the common placement tail of the actual loop body.
macro "finish_checked " c:term ", " st:term ", " hp:term ", " hn:term ", " expected:term ", " advance:term : tactic => `(tactic| (
  try rw [index_eq (⟨$c, ($hp).in_bounds⟩ : Fin ($st).stack.length)]
  try simp only [except_ok_bind]
  try rw [requires_of_true (¬ ($st).isFinal ⟨$c, ($hp).in_bounds⟩)
    ((($st).isFinal_iff ⟨$c, ($hp).in_bounds⟩).not.mpr $hn)]
  try simp only [not_false_eq_true, requires_of_true True True.intro, except_ok_bind, except_error_bind, pure_bind, bind_assoc]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    have hbelow := Stack.belowOfNotTop ($st).stack ⟨$c, ($hp).in_bounds⟩ hnotTop
    by_cases hr : ($st).isSwapReachable ⟨$c, ($hp).in_bounds⟩
    · rw [ite_eq_right (not_not_intro hr)]
      try simp_loop
      apply (($hp).swap_final hbelow hr $hn).bind
      rintro final ⟨hinv, he⟩
      exact $advance _ hinv (he.trans $expected)
    · rw [ite_eq_left hr]
      exact True.intro
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop)) $expected))

theorem Spec.attach {x : Except Error α} {post : α → Prop} (h : Spec x post) :
    Spec x.attach (fun a => post a.val) := by
  cases x with
  | ok value => exact h
  | error err => cases err <;> exact h

-- The loop skips a final cursor only when the cursor is on the stack.
theorem skip_unless_final {final : Fin size → Prop} [DecidablePred final] {skip rest : Except Error α}
    (h : (hlt : offset < size) → ¬ final ⟨offset, hlt⟩) :
    (if offset < size then index size offset >>= (fun i => if final i then skip else rest)
      else rest) = rest := by
  by_cases hlt : offset < size
  · rw [ite_eq_left hlt, index_eq ⟨offset, hlt⟩, except_ok_bind, ite_eq_right (h hlt)]
  · rw [ite_eq_right hlt]

-- The loop generates at `offset` only when both checks hold. Otherwise it continues with `rest`.
theorem Spec.ite_index {A : Prop} [Decidable A] {B : Fin size → Prop} [DecidablePred B]
    {gen rest : Except Error α} {post : α → Prop} (hlt : A → offset < size)
    (hgen : (hA : A) → B ⟨offset, hlt hA⟩ → Spec gen post) (hrest : Spec rest post) :
    Spec (if A then index size offset >>= (fun i => if B i then gen else rest) else rest) post := by
  by_cases hA : A
  · rw [ite_eq_left hA, index_eq ⟨offset, hlt hA⟩, except_ok_bind]
    by_cases hB : B ⟨offset, hlt hA⟩
    · rw [ite_eq_left hB]; exact hgen hA hB
    · rw [ite_eq_right hB]; exact hrest
  · rw [ite_eq_right hA]; exact hrest

-- The loop returns the expected stack of its input state.
theorem loop_spec (cursor : ℕ) (state : State source target spills)
    (inv : state.invariant cursor) :
    Spec (buildBottomUp.loop cursor state) (fun r => r.1 = state.expectedStack) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    exact inv.expected_done hdone
  have hc : cursor < target.length := Nat.lt_of_not_ge hdone
  have advance (next : State source target spills) (hi : next.invariant (cursor + 1))
      (he : next.expectedStack = state.expectedStack) :
      Spec (buildBottomUp.loop (cursor + 1) next) (fun r => r.1 = state.expectedStack) :=
    (loop_spec (cursor + 1) next hi).mono (fun _ hr => hr.trans he)
  have retry (next : State source target spills) (hi : next.invariant cursor)
      (hlt : next.pending_generations < state.pending_generations)
      (he : next.expectedStack = state.expectedStack) :
      Spec (buildBottomUp.loop cursor next) (fun r => r.1 = state.expectedStack) :=
    (loop_spec cursor next hi).mono (fun _ hr => hr.trans he)
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact advance _ (inv.advance hfinal) rfl
  let dest : Fin target.length := ⟨cursor, hc⟩
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  by_cases hz : state.pending_generations = 0
  · have ht : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
    have hs := inv.size
    have hp := state.mapping.complete_of_target_total (by omega) ht
    simp only [hz, ↓reduceIte, requires_of_true _ hp.1, except_ok_bind]
    rw [requires_of_true (∀ i, (state.destinationOf i).isSome) hp.2, except_ok_bind]
    cases hperm : Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hp.1 hp.2) with
    | error err =>
      cases err
      simp [Except.mapError, Spec]
    | ok result =>
      simpa [Except.mapError, Spec] using
        (Shuffler.Permute.permute_applies_permutation_of_ok _ _ _ hperm).trans
          (expectedStack_permutation state hp.1 hp.2)
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
    apply (generate_contract state u hb (inv.available u)).attach.bind
    intro next hgen
    exact retry _ (hgen.invariant inv) (hgen.decreases inv) hgen.expected
  rw [dite_eq_right hurg]
  apply Spec.ite_index (fun hA => hA.2.2)
  · intro _ hB
    let top : Fin target.length := ⟨state.stack.length, by omega⟩
    have hb : state.mapping.symm top = none := by
      simpa [State.positionOf, top] using hB.1
    apply (generate_contract state top hb (inv.available top)).attach.bind
    intro next hgen
    exact retry _ (hgen.invariant inv) (hgen.decreases inv) hgen.expected
  rw [index_eq dest, except_ok_bind]
  rcases Option.eq_none_or_eq_some (state.positionOf dest) with hpos | ⟨carrier, hpos⟩
  · simp only [hpos]
    have hb : state.mapping.symm dest = none := hpos
    apply (generate_contract state dest hb (inv.available dest)).bind
    intro next hgen
    have hp := hgen.placement inv
    let current : Fin next.stack.length := ⟨cursor, hp.in_bounds⟩
    rw [index_eq current, except_ok_bind]
    by_cases hf : ∃ h, next.isFinal ⟨cursor, h⟩
    · rw [ite_eq_left ((next.isFinal_iff current).mpr hf)]
      exact advance _ (hp.toInvariant.advance hf) hgen.expected
    · rw [ite_eq_right ((next.isFinal_iff current).not.mpr hf)]
      finish_checked cursor, next, hp, hf, hgen.expected, advance
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
      · exact (expectedStack_retag state current carrier hequal).symm
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
    have he : retag.expectedStack = state.expectedStack :=
      (expectedStack_retag state pos carrier hequal).symm
    by_cases hplaced : pos.val = cursor
    · simp only [hplaced, ↓reduceIte]
      exact advance _ (hi.advance
        ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced)) he
    simp only [hplaced, ↓reduceIte]
    by_cases hnotTop : pos.val ≠ retag.stack.length - 1
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
      rw [index_eq (size := retag.stack.length) pos]
      simp only [except_ok_bind]
      have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
      by_cases hr : retag.isSwapReachable pos
      · rw [ite_eq_right (not_not_intro hr)]
        apply (hi.swap_bound (dest := dest) pos hd hbelow hr hplaced).bind
        rintro next ⟨hp, he'⟩
        finish_checked cursor, next, hp.1, hp.2, he'.trans he, advance
      · rw [ite_eq_left hr]
        exact True.intro
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, ↓reduceIte]
      have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
      finish_checked cursor, retag, hp.1, hp.2, he, advance
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

theorem buildBottomUp_spec (initial : State source target spills) (h : initial.Valid) :
    Spec (buildBottomUp initial h) (fun result => result.1 = initial.expectedStack) := by
  apply (loop_spec 0 initial (State.invariant.initial h)).bind
  intro ⟨res, trace⟩ he
  have hsize : res.length = target.length := by simp [show res = _ from he, State.expectedStack]
  simp only [requires_of_true _ hsize, except_ok_bind]
  exact he

end Shuffler.BuildBottomUp
