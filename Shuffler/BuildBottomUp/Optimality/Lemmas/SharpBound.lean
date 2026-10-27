import Shuffler.BuildBottomUp.Optimality.Lemmas.GeneralBound
import Shuffler.BuildBottomUp.Lemmas.ReachActions

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

--- Slack arithmetic -------------------------------------------------------------------------------

-- A lower bound on the part of `liveBudget` that a run leaves unused. The
-- arguments are the pending generations `p`, the live positions `live`, the
-- window positions `w`, and whether the target slot just above the stack is
-- bound (`nb`). With `live = w` every window position is live.
def needOf (p live w : ℕ) (nb : Bool) : ℕ :=
  if (0 < p ∧ live = w ∧ (2 ≤ w ∨ (w = 1 ∧ nb = true))) ∨ (p = 0 ∧ 3 ≤ live) then 2
  else if 0 < p ∨ 0 < live then 1 else 0

macro "need_arith" : tactic => `(tactic| (
  simp only [needOf, Bool.false_eq_true, and_false, or_false, and_true] at *
  split_ifs at * <;> omega))

-- In each step lemma below, `sc + 2 * live + 2 * p` is the budget before the
-- step and `sc' + 2 * live' + 2 * p'` is the budget after it.

theorem needOf_advance {p live live' w w' : ℕ} {nb : Bool} (hlive : live' = live)
    (hw : live ≤ w') (hw' : w' ≤ w) : needOf p live w nb ≤ needOf p live' w' nb := by
  cases nb <;> need_arith

theorem needOf_permute {live w cost : ℕ} {nb : Bool} (hcost : 2 * cost ≤ 3 * live) :
    cost + needOf 0 live w nb ≤ 2 * live := by
  cases nb <;> need_arith

theorem needOf_terminal {p live w : ℕ} {nb : Bool} : needOf p live w nb ≤ 2 * live + 2 * p := by
  cases nb <;> need_arith

-- A generation at `d` while the cursor stays. `L` is the stack length before it.
theorem needOf_generation {sc sc' p p' live live' w w' d L : ℕ} {nb nb' : Bool}
    (hbudget : sc' + 2 * live' + 2 * p' ≤ sc + 2 * live + 2 * p) (hp : p' + 1 = p)
    (hsc : sc' ≤ sc + 1) (hlow : d < L → live' ≤ live)
    (hhigh : L ≤ d → sc' = sc) (hd : d < L + p) (hnb : d = L → nb = false)
    (hw : 1 ≤ w → w' = w + 1) (hlw' : live' ≤ w') :
    sc' + 2 * live' + 2 * p' + needOf p live w nb ≤
      sc + 2 * live + 2 * p + needOf p' live' w' nb' := by
  by_cases hdl : d < L
  · have := hlow hdl
    cases nb <;> cases nb' <;> need_arith
  · have := hhigh (by omega)
    by_cases hdL : d = L
    · have := hnb hdL
      subst nb
      cases nb' <;> need_arith
    · cases nb <;> cases nb' <;> need_arith

-- A generation at the cursor, followed by the advance of the cursor.
theorem needOf_cursor_generation {sc sc' p p' live live' w w' : ℕ} {nb nb' : Bool}
    (hbudget : sc' + 2 * live' + 2 * p' ≤ sc + 2 * live + 2 * p) (hp : p' + 1 = p)
    (hsc : sc' ≤ sc + 1) (hw : w' = w) (hlw' : live' ≤ w') :
    sc' + 2 * live' + 2 * p' + needOf p live w nb ≤
      sc + 2 * live + 2 * p + needOf p' live' w' nb' := by
  cases nb <;> cases nb' <;> need_arith

-- A placement that only exchanges destinations.
theorem needOf_retag {sc sc' p p' live live' w w' : ℕ} {nb nb' : Bool}
    (hbudget : sc' + 2 * live' + 2 * p' ≤ sc + 2 * live + 2 * p) (hsc : sc' = sc)
    (hp : p' = p) (hpos : 0 < p) (hw : w' ≤ w) (hlw' : live' ≤ w') (hnb : nb' = nb) :
    sc' + 2 * live' + 2 * p' + needOf p live w nb ≤
      sc + 2 * live + 2 * p + needOf p' live' w' nb' := by
  subst nb'
  cases nb <;> need_arith

-- A placement with one swap.
theorem needOf_one_swap {sc sc' p p' live live' w w' : ℕ} {nb nb' : Bool}
    (hbudget : sc' + 2 * live' + 2 * p' + 1 ≤ sc + 2 * live + 2 * p) (hp : p' = p)
    (hpos : 0 < p) :
    sc' + 2 * live' + 2 * p' + needOf p live w nb ≤
      sc + 2 * live + 2 * p + needOf p' live' w' nb' := by
  cases nb <;> cases nb' <;> need_arith

-- A placement with two swaps. The cursor and the moved copy are both live.
theorem needOf_two_swaps {sc sc' p p' live live' w w' : ℕ} {nb nb' : Bool}
    (hbudget : sc' + 2 * live' + 2 * p' ≤ sc + 2 * live + 2 * p) (hsc : sc' = sc + 2)
    (hp : p' = p) (hpos : 0 < p) (hw : w' + 1 = w) (hlive : 2 ≤ live) (hlw' : live' ≤ w')
    (hnb : w < 15 → nb = true) (hnb' : nb' = nb) :
    sc' + 2 * live' + 2 * p' + needOf p live w nb ≤
      sc + 2 * live + 2 * p + needOf p' live' w' nb' := by
  subst nb'
  cases nb
  · have : 15 ≤ w := by
      by_contra h
      exact absurd (hnb (by omega)) (by decide)
    need_arith
  · need_arith

--- Window and need -------------------------------------------------------------------------------

-- The number of positions at or above the cursor, inside SWAP reach of the
-- top, and below the top.
def windowSize (cursor : ℕ) (state : State source target spills) : ℕ :=
  state.stack.length - 1 - max cursor (state.stack.length - (MAX_SWAP_DEPTH + 1))

theorem live_le_windowSize (cursor : ℕ) (state : State source target spills) :
    live cursor state ≤ windowSize cursor state := by
  have h : liveSet cursor state ⊆
      Finset.Ico (max cursor (state.stack.length - (MAX_SWAP_DEPTH + 1)))
        (state.stack.length - 1) := by
    intro p hp
    have := mem_liveSet.mp hp
    simp only [Finset.mem_Ico]
    omega
  exact (Finset.card_le_card h).trans (by simp [windowSize])

-- Whether the target slot just above the stack is bound to a stack position.
def nextBound (state : State source target spills) : Bool :=
  if h : state.stack.length < target.length then
    (state.positionOf ⟨state.stack.length, h⟩).isSome
  else false

theorem nextBound_eq {state next : State source target spills}
    (hlen : next.stack.length = state.stack.length)
    (h : ∀ dest : Fin target.length, ((next.mapping.symm dest).map Fin.val).isSome =
      ((state.mapping.symm dest).map Fin.val).isSome) :
    nextBound next = nextBound state := by
  unfold nextBound State.positionOf
  by_cases hlt : state.stack.length < target.length
  · rw [dite_eq_left (hlen ▸ hlt), dite_eq_left hlt]
    simpa using (congrArg (fun d => ((next.mapping.symm d).map Fin.val).isSome)
      (Fin.ext hlen : (⟨_, hlen ▸ hlt⟩ : Fin target.length) = ⟨_, hlt⟩)).trans (h _)
  · rw [dite_eq_right (hlen ▸ hlt), dite_eq_right hlt]

-- An unbound target slot just above the stack makes `nextBound` false.
private theorem nextBound_of_unbound {state : State source target spills}
    (top : Fin target.length) (htop : top.val = state.stack.length)
    (hb : state.mapping.symm top = none) : nextBound state = false := by
  obtain ⟨t, ht⟩ := top
  subst htop
  simp [nextBound, State.positionOf, ht, hb]

theorem nextBound_retag (state : State source target spills) (a b : Fin state.stack.length) :
    nextBound { state with mapping := state.mapping.swapDestinations a b } = nextBound state :=
  nextBound_eq rfl fun _ => by simp [Mapping.swapDestinations_symm_apply]

theorem Swapped.nextBound_eq {state next : State source target spills}
    {pos : Fin state.stack.length} (hs : Swapped state next pos) :
    nextBound next = nextBound state :=
  BBU.nextBound_eq hs.size fun dest => by
    rw [hs.mapping dest]
    simp [Mapping.swapDestinations_symm_apply]

-- The swaps of the rest of the run stay at least this far below `liveBudget`.
def need (cursor : ℕ) (state : State source target spills) : ℕ :=
  needOf state.pending_generations (live cursor state) (windowSize cursor state)
    (nextBound state)

--- Steps ------------------------------------------------------------------------------------------

theorem need_advance {cursor : ℕ} {state : State source target spills}
    (hf : ∃ h, state.isFinal ⟨cursor, h⟩) :
    liveBudget (cursor + 1) state + need cursor state ≤
      liveBudget cursor state + need (cursor + 1) state := by
  have hsub : liveSet cursor state ⊆ liveSet (cursor + 1) state := by
    intro p hp
    have h := mem_liveSet.mp hp
    have hne : p ≠ cursor := fun he => h.2.2.2 (he ▸ hf)
    exact mem_liveSet.mpr ⟨by omega, h.2⟩
  have heq : live (cursor + 1) state = live cursor state :=
    le_antisymm (Finset.card_le_card (liveSet_advance cursor state)) (Finset.card_le_card hsub)
  have hw := live_le_windowSize (cursor + 1) state
  have hn : need cursor state ≤ need (cursor + 1) state :=
    needOf_advance heq (heq ▸ hw) (by simp only [windowSize]; omega)
  unfold liveBudget
  omega

-- A generation away from the cursor while the cursor is close to the top.
theorem need_generation {cursor : ℕ} {state next : State source target spills}
    {dest : Fin target.length} (inv : state.invariant cursor)
    (hbound : state.mapping.symm dest = none)
    (hg : Generation state next dest) (hsw : GenerationSwap state next dest)
    (hpos : 0 < state.pending_generations)
    (hge : cursor ≤ dest.val) (hnear : state.stack.length - cursor < MAX_SWAP_DEPTH)
    (hfinal : dest.val < state.stack.length → ∃ h, next.isFinal ⟨dest, h⟩)
    (hnb : dest.val = state.stack.length → nextBound state = false) :
    liveBudget cursor next + need cursor state ≤ liveBudget cursor state + need cursor next := by
  have hbudget := liveBudget_generation inv hbound hg hsw
  have hp := hg.pending
  have hl := hg.size
  have hsize := inv.size
  have hdest := dest.isLt
  have hlow : dest.val < state.stack.length → live cursor next ≤ live cursor state := fun hd =>
    live_generation_final inv hbound hg (by omega) (by unfold MAX_SWAP_DEPTH at *; omega)
      (hfinal hd)
  have hhigh : state.stack.length ≤ dest.val →
      next.trace.swapCount = state.trace.swapCount := by
    intro hd
    rcases hsw with h | ⟨_, hbelow, _⟩
    · exact h
    · omega
  have hsc : next.trace.swapCount ≤ state.trace.swapCount + 1 := by
    rcases hsw with h | ⟨h, _⟩ <;> omega
  have hw : 1 ≤ windowSize cursor state →
      windowSize cursor next = windowSize cursor state + 1 := by
    simp only [windowSize, hl]
    unfold MAX_SWAP_DEPTH at *
    omega
  unfold liveBudget at hbudget ⊢
  exact needOf_generation hbudget (by omega) hsc hlow hhigh (by omega) hnb hw
    (live_le_windowSize cursor next)

-- A generation at the cursor, then a swap or nothing, then the advance.
theorem need_cursor_generation {cursor : ℕ} {state final : State source target spills}
    (hbudget : liveBudget (cursor + 1) final ≤ liveBudget cursor state)
    (hp : final.pending_generations + 1 = state.pending_generations)
    (hsc : final.trace.swapCount ≤ state.trace.swapCount + 1)
    (hlen : final.stack.length = state.stack.length + 1) :
    liveBudget (cursor + 1) final + need cursor state ≤
      liveBudget cursor state + need (cursor + 1) final := by
  have hw : windowSize (cursor + 1) final = windowSize cursor state := by
    simp only [windowSize, hlen]
    unfold MAX_SWAP_DEPTH
    omega
  unfold liveBudget at hbudget ⊢
  exact needOf_cursor_generation hbudget hp hsc hw (live_le_windowSize (cursor + 1) final)

-- A placement that exchanges destinations without a swap.
theorem need_retag {cursor : ℕ} {state next : State source target spills}
    (hbudget : liveBudget (cursor + 1) next ≤ liveBudget cursor state)
    (hsc : next.trace.swapCount = state.trace.swapCount)
    (hp : next.pending_generations = state.pending_generations)
    (hpos : 0 < state.pending_generations)
    (hlen : next.stack.length = state.stack.length) (hnb : nextBound next = nextBound state) :
    liveBudget (cursor + 1) next + need cursor state ≤
      liveBudget cursor state + need (cursor + 1) next := by
  have hw : windowSize (cursor + 1) next ≤ windowSize cursor state := by
    simp only [windowSize, hlen]
    omega
  unfold liveBudget at hbudget ⊢
  exact needOf_retag hbudget hsc hp hpos hw (live_le_windowSize (cursor + 1) next) hnb

-- A placement with one swap.
theorem need_one_swap {cursor : ℕ} {state next : State source target spills}
    (hbudget : liveBudget (cursor + 1) next + 1 ≤ liveBudget cursor state)
    (hp : next.pending_generations = state.pending_generations)
    (hpos : 0 < state.pending_generations) :
    liveBudget (cursor + 1) next + need cursor state ≤
      liveBudget cursor state + need (cursor + 1) next := by
  unfold liveBudget at hbudget ⊢
  exact needOf_one_swap hbudget hp hpos

-- A placement with two swaps, from a cursor inside reach.
theorem need_two_swaps {cursor : ℕ} {state next : State source target spills}
    (hbudget : liveBudget (cursor + 1) next ≤ liveBudget cursor state)
    (hsc : next.trace.swapCount = state.trace.swapCount + 2)
    (hp : next.pending_generations = state.pending_generations)
    (hpos : 0 < state.pending_generations)
    (hlen : next.stack.length = state.stack.length)
    (hreach : state.stack.length ≤ cursor + (MAX_SWAP_DEPTH + 1))
    (hbelow : cursor + 1 < state.stack.length) (hlive : 2 ≤ live cursor state)
    (hnb : state.stack.length - cursor < MAX_SWAP_DEPTH → nextBound state = true)
    (hnb' : nextBound next = nextBound state) :
    liveBudget (cursor + 1) next + need cursor state ≤
      liveBudget cursor state + need (cursor + 1) next := by
  have hw : windowSize (cursor + 1) next + 1 = windowSize cursor state := by
    simp only [windowSize, hlen]
    unfold MAX_SWAP_DEPTH at *
    omega
  have hnb15 : windowSize cursor state < 15 → nextBound state = true := by
    intro h
    apply hnb
    simp only [windowSize] at h
    unfold MAX_SWAP_DEPTH at *
    omega
  unfold liveBudget at hbudget ⊢
  exact needOf_two_swaps hbudget hsc hp hpos hw hlive (live_le_windowSize (cursor + 1) next)
    hnb15 hnb'

--- Loop -------------------------------------------------------------------------------------------

-- The facts of the swap that places the cursor.
structure PlacementSwap (cursor : ℕ) (state final : State source target spills) : Prop where
  budget : liveBudget (cursor + 1) final + 1 ≤ liveBudget cursor state
  swaps : final.trace.swapCount = state.trace.swapCount + 1
  pending : final.pending_generations = state.pending_generations
  size : final.stack.length = state.stack.length
  nextBound : nextBound final = nextBound state
  reach : state.stack.length ≤ cursor + (MAX_SWAP_DEPTH + 1)
  below : cursor + 1 < state.stack.length

theorem placement_swap_need {state : State source target spills} {dest : Fin target.length}
    (hp : Placement dest state) (hbelow : dest.val + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨dest.val, hp.in_bounds⟩)
    (hnfinal : ¬ ∃ h, state.isFinal ⟨dest, h⟩) :
    Spec (state.swapWith dest.val) (fun final => (final.invariant (dest.val + 1) ∧
      PlacementSwap dest.val state final) ∧ Extends state.trace final.trace) := by
  have hr := (Stack.isSwapReachable_iff_length _ _).mp hreach
  apply (Spec.and (placement_swap_live hp hbelow hreach hnfinal)
    (swap_spec state ⟨dest.val, hp.in_bounds⟩ hbelow hreach (fun hf => hnfinal ⟨_, hf⟩)).with_eq).mono
  rintro final ⟨⟨hinv, hb, hext⟩, hs, hrun⟩
  have hc := swap_counts state final dest.val hrun
  exact ⟨⟨hinv, hb, hc.swaps, hc.pending, hs.size, Swapped.nextBound_eq hs, hr, hbelow⟩,
    hext⟩

-- The first swap of a placement with two swaps.
theorem invariant_swap_bound_need {state : State source target spills} {dest : Fin target.length}
    (cursor : ℕ) (h : state.invariant dest.val) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hne : pos.val ≠ dest.val) :
    Spec (state.swapWith pos.val) (fun next =>
      ((Placement dest next ∧ ¬ ∃ h, next.isFinal ⟨dest, h⟩) ∧ next.stack.length = state.stack.length ∧
        liveBudget cursor next ≤ liveBudget cursor state + 1) ∧
      next.trace.swapCount = state.trace.swapCount + 1 ∧
      next.pending_generations = state.pending_generations ∧
      nextBound next = nextBound state) := by
  have hnf := state.boundNotFinal dest pos hbound hne
  apply Spec.and (invariant_swap_bound_live cursor h pos hbound hbelow hreach hne)
  apply (swap_spec state pos hbelow hreach hnf).with_eq.mono
  rintro next ⟨hs, hrun⟩
  have hc := swap_counts state next pos.val hrun
  exact ⟨hc.swaps, hc.pending, Swapped.nextBound_eq hs⟩

macro "finish_need " c:term ", " st:term ", " hp:term ", " hn:term ", " cost:term ", " costTop:term ", " advance:term : tactic => `(tactic| (
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
      apply (placement_swap_need $hp hbelow hr $hn).bind
      rintro final ⟨⟨hinv, hps⟩, _⟩
      exact $advance _ hinv ($cost final hps)
    · rw [ite_eq_left hr]
      exact True.intro
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop)) ($costTop (not_not.mp hnotTop))))

-- Each loop step keeps `liveBudget - need` from increasing. The final Permute
-- or the end of the loop leaves at least `need` of `liveBudget` unused.
theorem loop_need_bound (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) :
    Spec (buildBottomUp.loop cursor state)
      (fun result => result.2.swapCount + need cursor state ≤ liveBudget cursor state) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    have := needOf_terminal (p := state.pending_generations) (live := live cursor state)
      (w := windowSize cursor state) (nb := nextBound state)
    dsimp only [Spec, liveBudget, need, pure, Except.pure]
    omega
  have hc : cursor < target.length := Nat.lt_of_not_ge hdone
  have advance (next : State source target spills) (hi : next.invariant (cursor + 1))
      (hb : liveBudget (cursor + 1) next + need cursor state ≤
        liveBudget cursor state + need (cursor + 1) next) :
      Spec (buildBottomUp.loop (cursor + 1) next)
        (fun result => result.2.swapCount + need cursor state ≤ liveBudget cursor state) :=
    (loop_need_bound (cursor + 1) next hi).mono fun _ h => by omega
  have retry (next : State source target spills) (hi : next.invariant cursor)
      (hlt : next.pending_generations < state.pending_generations)
      (hb : liveBudget cursor next + need cursor state ≤
        liveBudget cursor state + need cursor next) :
      Spec (buildBottomUp.loop cursor next)
        (fun result => result.2.swapCount + need cursor state ≤ liveBudget cursor state) :=
    (loop_need_bound cursor next hi).mono fun _ h => by omega
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact advance _ (inv.advance hfinal) (need_advance hfinal)
  let dest : Fin target.length := ⟨cursor, hc⟩
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  have hsize := inv.size
  by_cases hz : state.pending_generations = 0
  · have ht : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
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
      have hb := needOf_permute (w := windowSize cursor state) (nb := nextBound state)
        (permute_le_live inv hc hp.1 hp.2 hperm)
      rw [swapCount_concat]
      simp only [need, liveBudget, hz] at hb ⊢
      omega
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
    have hge : cursor ≤ u.val := by
      by_contra hlt'
      exact not_isFinal_of_unbound u hb (inv.processed u (by omega))
    have hnear := hurg.2.2
    have hfin : Spec (state.generate u.val)
        (fun next => u.val < state.stack.length → ∃ h, next.isFinal ⟨u, h⟩) := by
      by_cases hle : u.val ≤ state.stack.length
      · exact (generate_final state u hb (inv.available u) hle
          (by unfold MAX_SWAP_DEPTH at *; omega)).mono fun _ h _ => h
      · exact (generate_budget_contract state u hb (inv.available u)).mono
          fun _ _ h => absurd h (by omega)
    apply (Spec.and (generate_budget_contract state u hb (inv.available u)) hfin).attach.bind
    intro next ⟨⟨hgen, hsw⟩, hfinal⟩
    exact retry _ (hgen.invariant inv) (hgen.decreases inv)
      (need_generation inv hb hgen hsw (by omega) hge hnear hfinal
        (fun he => nextBound_of_unbound u he hb))
  rw [dite_eq_right hurg]
  apply ite_index_rest (fun hA => hA.2.2)
  · intro htop hB
    let top : Fin target.length := ⟨state.stack.length, by omega⟩
    have hb : state.mapping.symm top = none := by
      simpa [State.positionOf, top] using hB.1
    apply (generate_budget_contract state top hb (inv.available top)).attach.bind
    intro next ⟨hgen, hsw⟩
    exact retry _ (hgen.invariant inv) (hgen.decreases inv)
      (need_generation inv hb hgen hsw (by omega) (le_of_lt htop.2.1) hB.2
        (fun h => absurd h (Nat.lt_irrefl _)) (fun _ => nextBound_of_unbound top rfl hb))
  intro hntop
  rw [index_eq dest, except_ok_bind]
  rcases Option.eq_none_or_eq_some (state.positionOf dest) with hpos | ⟨carrier, hpos⟩
  · simp only [hpos]
    have hb : state.mapping.symm dest = none := hpos
    apply (generate_budget_contract state dest hb (inv.available dest)).bind
    intro next ⟨hgen, hsw⟩
    have hp := hgen.placement inv
    have hcost : liveBudget cursor next ≤ liveBudget cursor state :=
      liveBudget_generation inv hb hgen hsw
    have hpend := hgen.pending
    have hlen := hgen.size
    let current : Fin next.stack.length := ⟨cursor, hp.in_bounds⟩
    rw [index_eq current, except_ok_bind]
    by_cases hf : ∃ h, next.isFinal ⟨cursor, h⟩
    · rw [ite_eq_left ((next.isFinal_iff current).mpr hf)]
      have hsc : next.trace.swapCount ≤ state.trace.swapCount + 1 := by
        rcases hsw with h | ⟨h, _⟩ <;> omega
      exact advance _ (hp.toInvariant.advance hf)
        (need_cursor_generation ((liveBudget_advance cursor next).trans hcost)
          (by omega) hsc hlen)
    · rw [ite_eq_right ((next.isFinal_iff current).not.mpr hf)]
      have hsc : next.trace.swapCount = state.trace.swapCount := by
        rcases hsw with h | ⟨_, _, _, h⟩
        · exact h
        · exact absurd h hf
      finish_need cursor, next, hp, hf,
        (fun final (hps : PlacementSwap cursor next final) =>
          need_cursor_generation (state := state) (final := final)
            (by have := hps.budget; omega) (by have := hps.pending; omega)
            (by have := hps.swaps; omega) (by have := hps.size; omega)),
        (fun _ => need_cursor_generation ((liveBudget_advance cursor next).trans hcost)
          (by omega) (by omega) hlen),
        advance
  · simp only [hpos]
    have hb : state.mapping.symm dest = some carrier := hpos
    have hge := inv.processed.bound_ge dest carrier hb le_rfl
    have hcurrent : cursor < state.stack.length := lt_of_le_of_lt hge carrier.isLt
    let current : Fin state.stack.length := ⟨cursor, hcurrent⟩
    have hcarrier := state.boundNotFinal_of_not_final dest carrier hb hnfinal
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
      · exact need_retag ((liveBudget_advance _ _).trans
          (liveBudget_retag state current carrier (fun hf => hnfinal ⟨_, hf⟩) hcarrier)) rfl rfl
          (by omega) rfl (nextBound_retag state current carrier)
    rw [ite_eq_right hequal, index_eq carrier]
    simp only [except_ok_bind]
    have hscan := (spec_iff_triple _ _).mpr (copyScan_triple state carrier carrier.val
      ⟨carrier, rfl, rfl, hcarrier⟩)
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
    have hposge := inv.not_final_ge pos hmovable
    have hi : retag.invariant cursor := inv.retag pos carrier hposge hge
    have hd : retag.mapping.symm dest = some pos := by simp [retag, hb]
    have hretag : liveBudget cursor retag ≤ liveBudget cursor state :=
      liveBudget_retag state pos carrier hmovable hcarrier
    have hlenr : retag.stack.length = state.stack.length := rfl
    have hscr : retag.trace.swapCount = state.trace.swapCount := rfl
    have hpr : retag.pending_generations = state.pending_generations := rfl
    have hnbr : nextBound retag = nextBound state := nextBound_retag state pos carrier
    by_cases hplaced : pos.val = cursor
    · simp only [hplaced, ↓reduceIte]
      exact advance _ (hi.advance
        ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced))
        (need_retag ((liveBudget_advance _ _).trans hretag) hscr hpr (by omega) hlenr hnbr)
    simp only [hplaced, ↓reduceIte]
    by_cases hnotTop : pos.val ≠ retag.stack.length - 1
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
      rw [index_eq (size := retag.stack.length) pos]
      simp only [except_ok_bind]
      have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
      by_cases hr : retag.isSwapReachable pos
      · rw [ite_eq_right (not_not_intro hr)]
        have hlive : state.stack.length ≤ cursor + (MAX_SWAP_DEPTH + 1) →
            2 ≤ live cursor state := by
          intro hcr
          have hpr' := (Stack.isSwapReachable_iff_length _ _).mp hr
          have hsub : ({cursor, pos.val} : Finset ℕ) ⊆ liveSet cursor state := by
            intro q hq
            rcases Finset.mem_insert.mp hq with rfl | hq
            · exact mem_liveSet.mpr ⟨le_rfl, hcr, by omega, hnfinal⟩
            · rw [Finset.mem_singleton.mp hq]
              exact mem_liveSet.mpr ⟨hposge, by omega, by omega, fun hf => hmovable hf.2⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_pair (Ne.symm hplaced)] at this
          exact this
        have hP : state.stack.length - cursor < MAX_SWAP_DEPTH →
            nextBound state = true := by
          intro hnear
          have hnone : urgent = none := by
            cases hu' : urgent with
            | none => rfl
            | some v =>
              exfalso
              apply hurg
              refine ⟨by simp [hu'], ?_, hnear⟩
              intro hv
              rw [hu'] at hv
              obtain ⟨hlt, h0⟩ := hu v hu'
              have hvd : (⟨v, hlt⟩ : Fin target.length) = dest := Fin.ext (Option.some.inj hv)
              rw [hvd, hpos] at h0
              cases h0
          have htl : state.stack.length < target.length := by omega
          by_contra hnb
          apply hntop
          refine ⟨⟨by simp [hnone], by omega, htl⟩, ?_, by omega⟩
          simpa [nextBound, htl] using hnb
        apply (invariant_swap_bound_need (dest := dest) cursor hi
          pos hd hbelow hr hplaced).bind
        rintro next ⟨⟨hp, hlen, hbud⟩, hsc1, hp1, hnb1⟩
        finish_need cursor, next, hp.1, hp.2,
          (fun final (hps : PlacementSwap cursor next final) =>
            need_two_swaps (state := state) (next := final)
              (by have := hps.budget; omega) (by have := hps.swaps; omega)
              (by have := hps.pending; omega) (by omega)
              (by have := hps.size; omega)
              (by have := hps.reach; omega) (by have := hps.below; omega)
              (hlive (by have := hps.reach; omega)) hP
              (hps.nextBound.trans (hnb1.trans hnbr))),
          (fun h => absurd h (by omega)), advance
      · rw [ite_eq_left hr]
        exact True.intro
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, ↓reduceIte]
      have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
      finish_need cursor, retag, hp.1, hp.2,
        (fun final (hps : PlacementSwap cursor retag final) =>
          need_one_swap (state := state) (next := final)
            (by have := hps.budget; omega) (by have := hps.pending; omega)
            (by omega)),
        (fun h => absurd h (by omega)), advance
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

--- Main results -----------------------------------------------------------------------------------

theorem buildBottomUp_need_bound (initial : State source target spills) (h : initial.Valid)
    {result : Stack} {trace : Trace spills source result}
    (hrun : buildBottomUp initial h = .ok ⟨result, trace⟩) :
    trace.swapCount + need 0 initial ≤ liveBudget 0 initial := by
  have hs := loop_need_bound 0 initial (State.invariant.initial h)
  rw [loop_eq_of_ok hrun] at hs
  exact hs

end Shuffler.Optimality.BBU
