import Shuffler.BuildBottomUp.Lemmas.ReachScan
import Shuffler.BuildBottomUp.Lemmas.LoopProofs

open Std.Internal.Do

set_option mvcgen.warning false

namespace Shuffler.BuildBottomUp

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem State.invariant.permutation_reachable {state : State source target spills}
    (inv : state.invariant cursor) (hr : state.withinReach cursor)
    (hlen : state.stack.length = target.length) (hsource : ∀ i, (state.mapping i).isSome) :
    Shuffler.Permute.all_swaps_reachable (state.mapping.toPermutation hlen hsource) := by
  intro i hi
  have hge : cursor ≤ i.val := by
    by_contra hn
    let j : Fin target.length := Fin.cast hlen i
    have hf := inv.processed j (by change i.val < cursor; omega)
    have hb : state.mapping.symm j = some i :=
      state.boundOfVal j i (by
        rw [State.exists_isFinal_iff] at hf
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
  try rw [index_eq (⟨$c, ($hp).in_bounds⟩ : Fin ($st).stack.length)]
  try simp only [except_ok_bind]
  try rw [requires_of_true (¬ ($st).isFinal ⟨$c, ($hp).in_bounds⟩)
    ((($st).isFinal_iff ⟨$c, ($hp).in_bounds⟩).not.mpr $hn)]
  try simp only [not_false_eq_true, requires_of_true True True.intro, except_ok_bind, except_error_bind, pure_bind, bind_assoc]
  by_cases hnotTop : $c ≠ ($st).stack.length - 1
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
    let pos : Fin ($st).stack.length := ⟨$c, ($hp).in_bounds⟩
    have hreach := ($hr).swap_reachable pos (by rfl)
    rw [ite_eq_right (not_not_intro (show ($st).isSwapReachable pos from hreach))]
    try simp_loop
    have hbelow := Stack.belowOfNotTop ($st).stack pos hnotTop
    apply (($hp).swap_final_success $hr hbelow $hn).bind
    rintro next ⟨hi, hreach⟩
    exact $advance _ hi hreach
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop)) ($hr).advance))

theorem Succeeds.attach {x : Except Error α} {post : α → Prop} (h : Succeeds x post) :
    Succeeds x.attach (fun a => post a.val) := by
  obtain ⟨value, rfl, hv⟩ := h
  exact ⟨⟨value, rfl⟩, rfl, hv⟩

-- A successful result also satisfies every spec of its computation.
theorem Succeeds.spec {x : Except Error α} {pre post : α → Prop} (h : Succeeds x pre)
    (hs : Spec x post) : Succeeds x post := by
  obtain ⟨value, rfl, _⟩ := h
  exact ⟨value, rfl, hs⟩

-- The loop generates at `offset` only when both checks hold. Otherwise it continues with `rest`.
theorem Succeeds.ite_index {A : Prop} [Decidable A] {B : Fin size → Prop} [DecidablePred B]
    {gen rest : Except Error α} {post : α → Prop} (hlt : A → offset < size)
    (hgen : (hA : A) → B ⟨offset, hlt hA⟩ → Succeeds gen post) (hrest : Succeeds rest post) :
    Succeeds (if A then index size offset >>= (fun i => if B i then gen else rest) else rest) post := by
  by_cases hA : A
  · rw [ite_eq_left hA, index_eq ⟨offset, hlt hA⟩, except_ok_bind]
    by_cases hB : B ⟨offset, hlt hA⟩
    · rw [ite_eq_left hB]; exact hgen hA hB
    · rw [ite_eq_right hB]; exact hrest
  · rw [ite_eq_right hA]; exact hrest

-- The generate-at-top branch falls through when its inner check fails at every index.
theorem ite_index_eq_rest {A : Prop} [Decidable A] {B : Fin size → Prop} [DecidablePred B]
    {gen rest : Except Error α} (hlt : A → offset < size) (h : ∀ i, ¬ B i) :
    (if A then index size offset >>= (fun i => if B i then gen else rest) else rest) = rest := by
  by_cases hA : A
  · rw [ite_eq_left hA, index_eq ⟨offset, hlt hA⟩, except_ok_bind, ite_eq_right (h _)]
  · rw [ite_eq_right hA]

theorem loop_success (cursor : ℕ) (state : State source target spills)
    (inv : state.invariant cursor) (hr : state.withinReach cursor) :
    Succeeds (buildBottomUp.loop cursor state) (fun _ => True) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    exact ⟨_, rfl, trivial⟩
  have hc : cursor < target.length := Nat.lt_of_not_ge hdone
  have advance (next : State source target spills) (hi : next.invariant (cursor + 1))
      (hr : next.withinReach (cursor + 1)) :
      Succeeds (buildBottomUp.loop (cursor + 1) next) (fun _ => True) :=
    loop_success (cursor + 1) next hi hr
  have retry (next : State source target spills) (hi : next.invariant cursor)
      (hr : next.withinReach cursor) (hlt : next.pending_generations < state.pending_generations) :
      Succeeds (buildBottomUp.loop cursor next) (fun _ => True) :=
    loop_success cursor next hi hr
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact advance _ (inv.advance hfinal) hr.advance
  let dest : Fin target.length := ⟨cursor, hc⟩
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  by_cases hz : state.pending_generations = 0
  · have ht : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
    have hs := inv.size
    have hp := state.mapping.complete_of_target_total (by omega) ht
    simp only [hz, ↓reduceIte, requires_of_true _ hp.1, except_ok_bind]
    rw [requires_of_true (∀ i, (state.destinationOf i).isSome) hp.2, except_ok_bind]
    obtain ⟨res, trace, heq, _⟩ := Shuffler.Permute.permute_applies_permutation_reachable
      spills state.stack (state.mapping.toPermutation hp.1 hp.2)
      (inv.permutation_reachable hr hp.1 hp.2)
    simp only [heq, Except.mapError, except_ok_bind]
    exact ⟨_, rfl, trivial⟩
  simp only [hz, ↓reduceIte]
  have hscan := Succeeds.of_triple _ _ (urgentScan_success cursor state hr.copies)
  simp only [bind_pure] at hscan
  apply hscan.bind
  intro urgent hu
  by_cases hurg : urgent.isSome ∧ urgent ≠ some cursor ∧ state.stack.length - cursor < MAX_SWAP_DEPTH
  · rw [dite_eq_left hurg]
    obtain ⟨hlt, hnone⟩ := hu.choice (urgent.get hurg.1) (Option.some_get hurg.1).symm
    let u : Fin target.length := ⟨urgent.get hurg.1, hlt⟩
    have hb : state.mapping.symm u = none := by
      simpa [State.positionOf, hlt, u] using hnone
    have hready : Ready state u := (hu.selected u.val (Option.some_get hurg.1).symm).ready
    apply (generate_reachable state u hb (inv.available u) hr
      (inv.processed.unbound_ge u hb) hready).attach.bind
    rintro next ⟨hg, hcopies, _⟩
    apply retry _ (hg.invariant inv) ⟨?_, hcopies⟩ (hg.decreases inv)
    have := hg.size
    have := hurg.2.2
    have := inv.cursor_le_length hc
    omega
  rw [dite_eq_right hurg]
  apply Succeeds.ite_index (fun hA => hA.2.2)
  · intro hA hB
    let top : Fin target.length := ⟨state.stack.length, hA.2.2⟩
    have hb : state.mapping.symm top = none := by
      simpa [State.positionOf, top] using hB.1
    have hn : urgent = none := Option.isNone_iff_eq_none.mp hA.1
    have hready : Ready state top := (hn ▸ hu).ready_none inv.processed hB.2 top
    apply (generate_reachable state top hb (inv.available top) hr
      (Nat.le_of_lt hA.2.1) hready).attach.bind
    rintro next ⟨hg, hcopies, _⟩
    apply retry _ (hg.invariant inv) ⟨?_, hcopies⟩ (hg.decreases inv)
    have := hg.size
    have := hB.2
    have := inv.cursor_le_length hc
    omega
  rw [index_eq dest, except_ok_bind]
  rcases Option.eq_none_or_eq_some (state.positionOf dest) with hpos | ⟨carrier, hpos⟩
  · simp only [hpos]
    have hb : state.mapping.symm dest = none := hpos
    apply (generate_reachable state dest hb (inv.available dest) hr le_rfl
      (hu.ready_cursor inv.processed hr hc hurg)).bind
    rintro next ⟨hg, hcopies, hf⟩
    have hfinal := hf (inv.cursor_le_length hc)
    change (∃ h, next.isFinal ⟨cursor, h⟩) at hfinal
    have hp := hg.placement inv
    let current : Fin next.stack.length := ⟨cursor, hp.in_bounds⟩
    rw [index_eq current, except_ok_bind, ite_eq_left ((next.isFinal_iff current).mpr hfinal)]
    apply advance _ ((hg.invariant inv).advance hfinal) ⟨?_, hcopies⟩
    have := hg.size
    have := hr.width
    have := inv.cursor_le_length hc
    omega
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
      apply advance _ _ (hr.retag current carrier).advance
      apply hi.advance
      have hd : (state.mapping.swapDestinations current carrier).symm dest = some current := by
        simp [hb]
      exact (State.isFinal_of_bound_iff
        { state with mapping := state.mapping.swapDestinations current carrier }
        dest current hd).mpr rfl
    rw [ite_eq_right hequal, index_eq carrier]
    simp only [except_ok_bind]
    have hscan := Succeeds.of_triple _ _ (copyScan_success state carrier carrier.val
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
    have hrt : retag.withinReach cursor := hr.retag pos carrier
    have hd : retag.mapping.symm dest = some pos := by simp [retag, hb]
    by_cases hplaced : pos.val = cursor
    · simp only [hplaced, ↓reduceIte]
      exact advance _ (hi.advance
        ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced)) hrt.advance
    simp only [hplaced, ↓reduceIte]
    by_cases hnotTop : pos.val ≠ retag.stack.length - 1
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
      rw [index_eq (size := retag.stack.length) pos]
      simp only [except_ok_bind]
      have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
      have hreach := hrt.swap_reachable pos (hi.processed.bound_ge dest pos hd le_rfl)
      rw [ite_eq_right (not_not_intro (show retag.isSwapReachable pos from hreach))]
      apply (hi.swap_bound_success (dest := dest) hrt pos hd hbelow hplaced).bind
      rintro next ⟨hp, hrn⟩
      finish_reachable cursor, next, hp.1, hp.2, hrn, advance
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, ↓reduceIte]
      have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
      finish_reachable cursor, retag, hp.1, hp.2, hrt, advance
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

-- The size check after the loop holds whenever the loop succeeds.
theorem buildBottomUp_success_iff_loop (initial : State source target spills) (h : initial.Valid) :
    Succeeds (buildBottomUp initial h) (fun _ => True) ↔
      Succeeds (buildBottomUp.loop 0 initial) (fun _ => True) := by
  constructor
  · intro hs
    unfold buildBottomUp at hs
    cases hl : buildBottomUp.loop 0 initial with
    | error err =>
      rw [hl] at hs
      obtain ⟨_, he, _⟩ := hs
      cases he
    | ok value => exact ⟨value, rfl, trivial⟩
  · intro hs
    unfold buildBottomUp
    apply (hs.spec (loop_spec 0 initial (State.invariant.initial h))).bind
    intro ⟨res, trace⟩ he
    have hsize : res.length = target.length := by simp [show res = _ from he, State.expectedStack]
    simp only [requires_of_true _ hsize, except_ok_bind]
    exact ⟨_, rfl, trivial⟩

theorem buildBottomUp_success (initial : State source target spills) (h : initial.Valid)
    (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1) :
    Succeeds (buildBottomUp initial h) (fun _ => True) :=
  (buildBottomUp_success_iff_loop initial h).mpr
    (loop_success 0 initial (State.invariant.initial h) (State.withinReach.initial h hsmall))

-- The loop skips a final prefix without changing the state.
theorem loop_zero_eq_of_processed (state : State source target spills)
    (hp : state.processed cursor) :
    buildBottomUp.loop 0 state = buildBottomUp.loop cursor state := by
  induction cursor with
  | zero => rfl
  | succ cursor ih =>
    rw [ih (fun i hi => hp i (by omega))]
    by_cases hc : cursor < target.length
    · have hf := hp ⟨cursor, hc⟩ (by simp)
      have hs := hf.1
      rw [buildBottomUp.loop.eq_def]
      simp only [show ¬ cursor ≥ target.length by omega,
        ↓reduceIte]
      rw [ite_eq_left hs, index_eq ⟨cursor, hs⟩, except_ok_bind,
        ite_eq_left ((state.isFinal_iff ⟨cursor, hs⟩).mpr hf)]
    · have hn : ¬cursor + 1 < target.length := by omega
      conv_lhs => rw [buildBottomUp.loop.eq_def]
      conv_rhs => rw [buildBottomUp.loop.eq_def]
      simp only [show cursor ≥ target.length by omega, show cursor + 1 ≥ target.length by omega,
        ↓reduceIte]

theorem buildBottomUp_success_of_processed (initial : State source target spills)
    (h : initial.Valid) (hp : initial.processed cursor) (hr : initial.withinReach cursor) :
    Succeeds (buildBottomUp initial h) (fun _ => True) := by
  rw [buildBottomUp_success_iff_loop, loop_zero_eq_of_processed initial hp]
  exact loop_success cursor initial ⟨h, hp⟩ hr

end Shuffler.BuildBottomUp
