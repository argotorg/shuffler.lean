import Shuffler.BuildBottomUp.Optimality.Lemmas.LoopExtends

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

-- A position is live when it is at or above the cursor, inside SWAP reach of
-- the top, below the top, and does not hold its own destination.
def liveSet (cursor : ℕ) (state : State source target spills) : Finset ℕ :=
  (Finset.range state.stack.length).filter fun p =>
    cursor ≤ p ∧ state.stack.length ≤ p + (MAX_SWAP_DEPTH + 1) ∧
      p + 1 < state.stack.length ∧ ¬ ∃ h, state.isFinal ⟨p, h⟩

def live (cursor : ℕ) (state : State source target spills) : ℕ :=
  (liveSet cursor state).card

-- A Spec and an independent fact about every successful result combine.
private theorem Spec.and_ok {result : Except Error α} {post extra : α → Prop}
    (h : Spec result post) (hextra : ∀ value, result = .ok value → extra value) :
    Spec result (fun value => post value ∧ extra value) := by
  cases result with
  | ok value => exact ⟨h, hextra value rfl⟩
  | error err => cases err <;> exact h

theorem produce_swapCount_triple (state : State source target spills)
    (dest : Fin target.length) :
    ⦃True⦄ state.produce dest
      ⦃fun s => s.trace.swapCount = state.trace.swapCount; epost⟨fun _ => True⟩⦄ := by
  vcgen [State.produce, State.push, State.dup, requires, index]
  all_goals simp_all [Trace.swapCount]
  all_goals
    generalize hv : target[dest.val] = value at *
    cases value <;> simp_all [Trace.swapCount, Value.can_be_freely_generated, SpillSet.is_spilled]
  all_goals
    have h : Value.FunctionReturnLabel.can_be_freely_generated ∨
        SpillSet.is_spilled spills Value.FunctionReturnLabel := by assumption
    simp [Value.can_be_freely_generated, SpillSet.is_spilled] at h

private theorem ok_of_triple_true {x : Except Error α} {post : α → Prop}
    (h : ⦃True⦄ x ⦃post; epost⟨fun _ => True⟩⦄) : ∀ value, x = .ok value → post value := by
  intro value hv
  have hp := h.le_wp trivial
  rw [hv] at hp
  exact hp

@[spec] theorem produce_counted_spec (state : State source target spills)
    (dest : Fin target.length) (hbound : state.mapping.symm dest = none)
    (havailable : state.isAvailable dest) :
    ⦃True⦄ state.produce dest
    ⦃fun next => Growth state next dest (state.pending_generations - 1) ∧
      next.trace.swapCount = state.trace.swapCount; allowedErrors⦄ := by
  apply (spec_iff_triple _ _).mp
  exact Spec.and_ok ((spec_iff_triple _ _).mpr (produce_spec state dest hbound havailable))
    (ok_of_triple_true (produce_swapCount_triple state dest))

private theorem swapWith_swapCount_triple (state : State source target spills) (offset : ℕ) :
    ⦃True⦄ state.swapWith offset
      ⦃fun s => s.trace.swapCount = state.trace.swapCount + 1; epost⟨fun _ => True⟩⦄ := by
  vcgen [State.swapWith, requires, index]
  all_goals simp [Trace.swapCount]

@[spec] theorem swapWith_counted_spec (state : State source target spills) (offset : ℕ)
    (hlt : offset < state.stack.length) (hbelow : offset + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨offset, hlt⟩) (hnfinal : ¬ state.isFinal ⟨offset, hlt⟩) :
    ⦃True⦄ state.swapWith offset
    ⦃fun next => Swapped state next ⟨offset, hlt⟩ ∧
      next.trace.swapCount = state.trace.swapCount + 1; allowedErrors⦄ := by
  apply (spec_iff_triple _ _).mp
  exact Spec.and_ok ((spec_iff_triple _ _).mpr
      (swapWith_spec state offset hlt hbelow hreach hnfinal))
    (ok_of_triple_true (swapWith_swapCount_triple state offset))

-- A generation emits a swap only when it makes `dest` final inside reach.
def GenerationSwap (state next : State source target spills) (dest : Fin target.length) : Prop :=
  next.trace.swapCount = state.trace.swapCount ∨
    (next.trace.swapCount = state.trace.swapCount + 1 ∧ dest.val + 1 < next.stack.length ∧
      next.stack.length ≤ dest.val + (MAX_SWAP_DEPTH + 1) ∧ ∃ h, next.isFinal ⟨dest, h⟩)

private theorem generationSwap_of_swap {state produced next : State source target spills}
    {dest : Fin target.length}
    (hg : Growth state produced dest (state.pending_generations - 1) ∧
      produced.trace.swapCount = state.trace.swapCount)
    (hlt : dest.val < produced.stack.length) (hbelow : dest.val + 1 < produced.stack.length)
    (hreach : produced.stack.isSwapReachable ⟨dest.val, hlt⟩)
    (hs : Swapped produced next ⟨dest.val, hlt⟩ ∧
      next.trace.swapCount = produced.trace.swapCount + 1) :
    GenerationSwap state next dest := by
  have htop : (produced.mapping.symm dest).map Fin.val = some (produced.stack.length - 1) := by
    simpa [State.positionOf, dest.isLt] using hg.1.top
  refine Or.inr ⟨by omega, by rw [hs.1.size]; exact hbelow, ?_, hs.1.final dest rfl htop⟩
  have := hs.1.size
  simp only [Stack.isSwapReachable, Stack.offsetToDepth] at hreach
  unfold MAX_SWAP_DEPTH at *
  omega

private theorem generate_swap_triple (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    ⦃True⦄ state.generate dest.val
    ⦃fun next => GenerationSwap state next dest; allowedErrors⦄ := by
  vcgen [State.generate, produce_counted_spec, swapWith_counted_spec]
  all_goals try simp only [Fin.val_inj] at *
  all_goals subst_vars
  all_goals first
    | assumption
    | exact State.not_isFinal_of_val_eq (by assumption) (by assumption)
    | exact Or.inl (by assumption : _ ∧ _).2
    | exact (by assumption : _ ∧ _).2
    | omega
    | solve | simp_all
    | (simp only [State.isSwapReachable, State.depthOf, Stack.isSwapReachable,
        Stack.offsetToDepth] at *; omega)
    | skip
  case vc7 =>
    rename_i hg _ _ pos hr _ _ hbelow _ hpos _ hs
    obtain ⟨p, hp⟩ := pos
    dsimp only at hpos
    subst hpos
    exact generationSwap_of_swap hg _ hbelow hr hs

-- Every successful generation satisfies both contracts.
theorem generate_budget_contract (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    Spec (state.generate dest.val)
      (fun next => Generation state next dest ∧ GenerationSwap state next dest) := by
  have hs := (spec_iff_triple _ _).mpr (generate_swap_triple state dest hbound havailable)
  have hg := generate_contract state dest hbound havailable
  cases h : state.generate dest.val with
  | ok next => rw [h] at hs hg; exact ⟨hg, hs⟩
  | error err => rw [h] at hg; cases err <;> trivial

--- Live positions ---------------------------------------------------------------------------------

-- Each step keeps the emitted swaps plus this potential from increasing.
def liveBudget (cursor : ℕ) (state : State source target spills) : ℕ :=
  state.trace.swapCount + 2 * live cursor state + 2 * state.pending_generations

theorem mem_liveSet {cursor p : ℕ} {state : State source target spills} :
    p ∈ liveSet cursor state ↔ cursor ≤ p ∧
      state.stack.length ≤ p + (MAX_SWAP_DEPTH + 1) ∧
      p + 1 < state.stack.length ∧ ¬ ∃ h, state.isFinal ⟨p, h⟩ := by
  simp only [liveSet, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  omega

-- The window holds seventeen positions, and the top is not live.
theorem live_le_window (cursor : ℕ) (state : State source target spills) :
    live cursor state ≤ min state.stack.length (MAX_SWAP_DEPTH + 1) - 1 := by
  have h : liveSet cursor state ⊆
      Finset.Ico (state.stack.length - (MAX_SWAP_DEPTH + 1)) (state.stack.length - 1) := by
    intro p hp
    have := mem_liveSet.mp hp
    simp only [Finset.mem_Ico]
    omega
  exact (Finset.card_le_card h).trans (by simp only [Nat.card_Ico]; omega)

theorem liveSet_advance (cursor : ℕ) (state : State source target spills) :
    liveSet (cursor + 1) state ⊆ liveSet cursor state := by
  intro p hp
  have := mem_liveSet.mp hp
  exact mem_liveSet.mpr ⟨by omega, this.2⟩

theorem liveBudget_advance (cursor : ℕ) (state : State source target spills) :
    liveBudget (cursor + 1) state ≤ liveBudget cursor state := by
  have := Finset.card_le_card (liveSet_advance cursor state)
  unfold liveBudget live
  omega

-- Same length; every non-top position that is not final afterwards was not final before.
theorem liveSet_subset {cursor cursor' : ℕ} {state next : State source target spills}
    (hc : cursor ≤ cursor') (hlen : next.stack.length = state.stack.length)
    (h : ∀ p, cursor' ≤ p → p + 1 < state.stack.length → ¬ (∃ h, next.isFinal ⟨p, h⟩) →
      ¬ ∃ h, state.isFinal ⟨p, h⟩) :
    liveSet cursor' next ⊆ liveSet cursor state := by
  intro p hp
  obtain ⟨hcp, hw, htop, hnf⟩ := mem_liveSet.mp hp
  rw [hlen] at hw htop
  exact mem_liveSet.mpr ⟨by omega, hw, htop, h p hcp htop hnf⟩

theorem isFinal_lt_target {state : State source target spills} {p : ℕ}
    (h : ∃ h, state.isFinal ⟨p, h⟩) : p < target.length := by
  rw [State.exists_isFinal_iff] at h
  split at h
  · assumption
  · exact h.elim

theorem not_isFinal_of_unbound {state : State source target spills} (dest : Fin target.length)
    (h : state.mapping.symm dest = none) : ¬ ∃ h, state.isFinal ⟨dest, h⟩ := by
  simp [State.exists_isFinal_iff, dest.isLt, h]

-- Exchanging the destinations of a and b leaves the finality of other positions unchanged.
theorem isFinal_swapDestinations_iff {state next : State source target spills}
    (a b : Fin state.stack.length)
    (hmap : ∀ dest : Fin target.length, (next.mapping.symm dest).map Fin.val =
      ((state.mapping.swapDestinations a b).symm dest).map Fin.val)
    {p : ℕ} (ha : p ≠ a.val) (hb : p ≠ b.val) :
    (∃ h, next.isFinal ⟨p, h⟩) ↔ ∃ h, state.isFinal ⟨p, h⟩ := by
  rw [State.exists_isFinal_iff, State.exists_isFinal_iff]
  split
  · rename_i hp
    rw [hmap, Mapping.swapDestinations_symm_apply]
    rcases hq : state.mapping.symm ⟨p, hp⟩ with _ | q
    · simp
    · simp only [Option.map_some, Option.some.injEq]
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst q; constructor <;> intro h <;> omega
      · subst q; constructor <;> intro h <;> omega
      · rfl
  · rfl

theorem liveSet_retag {cursor : ℕ} (state : State source target spills)
    (a b : Fin state.stack.length) (ha : ¬ state.isFinal a) (hb : ¬ state.isFinal b) :
    liveSet cursor { state with mapping := state.mapping.swapDestinations a b } ⊆
      liveSet cursor state := by
  refine liveSet_subset le_rfl rfl ?_
  intro p _ _ hnf
  by_cases hpa : p = a.val
  · subst hpa; exact fun hf => ha hf.2
  by_cases hpb : p = b.val
  · subst hpb; exact fun hf => hb hf.2
  exact (isFinal_swapDestinations_iff (next := { state with
    mapping := state.mapping.swapDestinations a b }) a b (fun _ => rfl) hpa hpb).not.mp hnf

theorem liveBudget_retag {cursor : ℕ} (state : State source target spills)
    (a b : Fin state.stack.length) (ha : ¬ state.isFinal a) (hb : ¬ state.isFinal b) :
    liveBudget cursor { state with mapping := state.mapping.swapDestinations a b } ≤
      liveBudget cursor state := by
  have := Finset.card_le_card (liveSet_retag (cursor := cursor) state a b ha hb)
  unfold liveBudget live
  dsimp only
  omega

-- A swap with a non-final position adds one swap and no live position.
theorem liveSet_swapped {cursor : ℕ} {state next : State source target spills}
    {pos : Fin state.stack.length} (hs : Swapped state next pos)
    (hnf : ¬ state.isFinal pos) : liveSet cursor next ⊆ liveSet cursor state := by
  apply liveSet_subset le_rfl hs.size
  intro p _ hlt hnext
  by_cases hpa : p = pos.val
  · subst hpa; exact fun hf => hnf hf.2
  exact (isFinal_swapDestinations_iff pos _ hs.mapping hpa (by dsimp; omega)).not.mp hnext

theorem placement_swap_live {state : State source target spills} {dest : Fin target.length}
    (hp : Placement dest state) (hbelow : dest.val + 1 < state.stack.length)
    (hreach : state.stack.isSwapReachable ⟨dest.val, hp.in_bounds⟩)
    (hnfinal : ¬ ∃ h, state.isFinal ⟨dest, h⟩) :
    Spec (state.swapWith dest.val) (fun next => next.invariant (dest.val + 1) ∧
      liveBudget (dest.val + 1) next + 1 ≤ liveBudget dest.val state ∧
      Extends state.trace next.trace) := by
  apply (swap_spec state ⟨dest.val, hp.in_bounds⟩ hbelow hreach (fun hf => hnfinal ⟨_, hf⟩)).with_eq.mono
  rintro next ⟨hs, hrun⟩
  have hcounts := swap_counts state next dest.val hrun
  refine ⟨(hs.invariant hp.toInvariant le_rfl).advance
    (hs.final dest rfl (hp.position.resolve_left hnfinal)), ?_, hcounts.extension⟩
  have hsub : liveSet (dest.val + 1) next ⊆ (liveSet dest.val state).erase dest.val := by
    intro p hpm
    have hpm' := mem_liveSet.mp hpm
    refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
    apply liveSet_subset (Nat.le_succ _) hs.size _ hpm
    intro q hq hlt hnext
    exact (isFinal_swapDestinations_iff ⟨dest.val, hp.in_bounds⟩ _ hs.mapping
      (by dsimp; omega) (by dsimp; omega)).not.mp hnext
  have hmem : dest.val ∈ liveSet dest.val state := by
    refine mem_liveSet.mpr ⟨le_rfl, ?_, hbelow, hnfinal⟩
    simp only [Stack.isSwapReachable, Stack.offsetToDepth] at hreach
    unfold MAX_SWAP_DEPTH at *
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at hc
  have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
  have := hcounts.swaps
  have := hcounts.pending
  unfold liveBudget live
  omega

-- A generation adds at most the old top to the live positions.
theorem liveSet_generation {cursor : ℕ} {state next : State source target spills}
    {dest : Fin target.length} (hg : Generation state next dest) :
    liveSet cursor next ⊆ insert (state.stack.length - 1) (liveSet cursor state) := by
  have hl := hg.size
  intro p hpm
  obtain ⟨hcp, hw, htop, hnf⟩ := mem_liveSet.mp hpm
  rw [hl] at hw htop
  by_cases hpl : p = state.stack.length - 1
  · exact Finset.mem_insert.mpr (Or.inl hpl)
  refine Finset.mem_insert.mpr (Or.inr (mem_liveSet.mpr ⟨hcp, by omega, by omega, ?_⟩))
  exact fun hs => hnf (hg.preserved ⟨p, isFinal_lt_target hs⟩ hs)

-- A generation that makes `dest` final inside reach adds no live position.
theorem live_generation_final {cursor : ℕ} {state next : State source target spills}
    {dest : Fin target.length} (inv : state.invariant cursor)
    (hbound : state.mapping.symm dest = none) (hg : Generation state next dest)
    (hbelow : dest.val + 1 < next.stack.length)
    (hreach : next.stack.length ≤ dest.val + (MAX_SWAP_DEPTH + 1)) (hfinal : ∃ h, next.isFinal ⟨dest, h⟩) :
    live cursor next ≤ live cursor state := by
  have hl := hg.size
  have hsub := liveSet_generation (cursor := cursor) hg
  have hnf := not_isFinal_of_unbound dest hbound
  have hge := inv.not_final_ge ⟨dest.val, by omega⟩ (fun hf => hnf ⟨_, hf⟩)
  have hmem : dest.val ∈ insert (state.stack.length - 1) (liveSet cursor state) := by
    by_cases htop : dest.val = state.stack.length - 1
    · exact Finset.mem_insert.mpr (Or.inl htop)
    · exact Finset.mem_insert.mpr (Or.inr (mem_liveSet.mpr ⟨hge, by omega, by omega, hnf⟩))
  have hsub' : liveSet cursor next ⊆
      (insert (state.stack.length - 1) (liveSet cursor state)).erase dest.val := by
    intro p hpm
    refine Finset.mem_erase.mpr ⟨?_, hsub hpm⟩
    rintro rfl
    exact (mem_liveSet.mp hpm).2.2.2 hfinal
  have hc := Finset.card_le_card hsub'
  rw [Finset.card_erase_of_mem hmem] at hc
  have := Finset.card_insert_le (state.stack.length - 1) (liveSet cursor state)
  unfold live
  omega

-- A generation makes the old top a non-top position. A generation that swaps
-- also makes `dest` final.
theorem liveBudget_generation {cursor : ℕ} {state next : State source target spills}
    {dest : Fin target.length} (inv : state.invariant cursor)
    (hbound : state.mapping.symm dest = none)
    (hg : Generation state next dest) (hsw : GenerationSwap state next dest) :
    liveBudget cursor next ≤ liveBudget cursor state := by
  have hpend := hg.decreases inv
  have hp := hg.pending
  rcases hsw with hsw | ⟨hsw, hbelow, hreach, hfinal⟩
  · have hc := (Finset.card_le_card (liveSet_generation (cursor := cursor) hg)).trans
      (Finset.card_insert_le _ _)
    unfold liveBudget live
    omega
  · have := live_generation_final inv hbound hg hbelow hreach hfinal
    unfold liveBudget
    omega

-- The final Permute moves only live positions. Its cycles that avoid the top
-- have at least two positions each, so it emits at most three swaps for each
-- two live positions.
theorem permute_le_live {cursor : ℕ} {state : State source target spills}
    (inv : state.invariant cursor) (hc : cursor < target.length)
    (hlen : state.stack.length = target.length) (hsource : ∀ i, (state.mapping i).isSome)
    {res : Stack} {trace : Trace spills state.stack res}
    (hrun : Shuffler.Permute.permute spills state.stack
      (state.mapping.toPermutation hlen hsource) = .ok ⟨res, trace⟩) :
    2 * trace.swapCount ≤ 3 * live cursor state := by
  have hne : 0 < state.stack.length := by omega
  let perm := state.mapping.toPermutation hlen hsource
  have hr : Shuffler.Permute.all_swaps_reachable perm := by
    by_contra hn
    obtain ⟨_, he, _⟩ := Shuffler.Permute.permute_blocks_unreachable spills state.stack perm hn
    rw [hrun] at he
    cases he
  rw [Shuffler.Permute.permute_swapCount spills state.stack perm hne hrun]
  have hcyc := two_mul_cyclesAway_le_support perm ⟨state.stack.length - 1, by omega⟩
  have hsupport : (perm.support.erase ⟨state.stack.length - 1, by omega⟩).card ≤
      live cursor state := by
    apply Finset.card_le_card_of_injOn (fun i => i.val)
    · intro i hi
      have hi' := Finset.mem_erase.mp (Finset.mem_coe.mp hi)
      have hmoved := Equiv.Perm.mem_support.mp hi'.2
      have hreach := hr i hi'.2
      have hnf : ¬ state.isFinal i := by
        intro hf
        apply hmoved
        let j : Fin target.length := Fin.cast hlen i
        have hb : state.mapping.symm j = some i :=
          state.boundOfVal j i (by
            rw [State.isFinal_iff, State.exists_isFinal_iff] at hf
            rw [dite_eq_left (show i.val < target.length from j.isLt)] at hf
            exact hf)
        have he := Mapping.toPermutation_apply state.mapping hlen hsource i
        rw [state.mapping.eq_some_iff.mp hb] at he
        have he' := congrArg Fin.val (Option.some.inj he)
        exact Fin.ext he'
      have hge := inv.not_final_ge i hnf
      have hne : i.val + 1 < state.stack.length := by
        have h1 := hi'.1
        have := i.isLt
        simp only [ne_eq, Fin.ext_iff] at h1
        omega
      refine Finset.mem_coe.mpr (mem_liveSet.mpr ⟨hge, ?_, hne, fun hf => hnf hf.2⟩)
      rw [Fin.val_rev] at hreach
      show state.stack.length ≤ i.val + (MAX_SWAP_DEPTH + 1)
      unfold MAX_SWAP_DEPTH at *
      omega
    · intro i _ j _ h
      exact Fin.ext h
  unfold Shuffler.Permute.Permutation.swapCount
  omega

theorem Spec.and {result : Except Error α} {p q : α → Prop}
    (hp : Spec result p) (hq : Spec result q) : Spec result (fun v => p v ∧ q v) := by
  cases result with
  | ok value => exact ⟨hp, hq⟩
  | error error => cases error <;> exact hp

-- The first swap of a bound placement adds one swap and no live position.
theorem invariant_swap_bound_live {state : State source target spills} {dest : Fin target.length}
    (cursor : ℕ) (h : state.invariant dest.val) (pos : Fin state.stack.length)
    (hbound : state.mapping.symm dest = some pos)
    (hbelow : pos.val + 1 < state.stack.length) (hreach : state.stack.isSwapReachable pos)
    (hne : pos.val ≠ dest.val) :
    Spec (state.swapWith pos.val) (fun next =>
      (Placement dest next ∧ ¬ ∃ h, next.isFinal ⟨dest, h⟩) ∧ next.stack.length = state.stack.length ∧
        liveBudget cursor next ≤ liveBudget cursor state + 1) := by
  have hnf := state.boundNotFinal dest pos hbound hne
  apply Spec.and ((h.swap_bound pos hbound hbelow hreach hne).mono fun _ hn => hn.1)
  apply (swap_spec state pos hbelow hreach hnf).with_eq.mono
  rintro next ⟨hs, hrun⟩
  have hcounts := swap_counts state next pos.val hrun
  have hc := Finset.card_le_card (liveSet_swapped (cursor := cursor) hs hnf)
  have := hcounts.swaps
  have := hcounts.pending
  refine ⟨hs.size, ?_⟩
  unfold liveBudget live
  omega

macro "finish_live " c:term ", " st:term ", " hp:term ", " hn:term ", " cost:term ", " costTop:term ", " advance:term : tactic => `(tactic| (
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
      apply (placement_swap_live $hp hbelow hr $hn).bind
      rintro final ⟨hinv, hb, _⟩
      have hb' : liveBudget ($c + 1) final + 1 ≤ liveBudget $c $st := hb
      exact $advance _ hinv (by have := $cost; omega)
    · rw [ite_eq_left hr]
      exact True.intro
  · try dsimp +zetaDelta only at hnotTop
    simp +zetaDelta only [ne_eq, hnotTop, ↓reduceIte]
    exact $advance _ (($hp).finish_at_top (not_not.mp hnotTop))
      ((liveBudget_advance $c $st).trans ($costTop (not_not.mp hnotTop)))))

-- Each loop step keeps `liveBudget` from increasing; the final Permute emits
-- at most two swaps for each live position.
theorem loop_live_bound (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) :
    Spec (buildBottomUp.loop cursor state)
      (fun result => result.2.swapCount ≤ liveBudget cursor state) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    dsimp [Spec, liveBudget, pure, Except.pure]
    omega
  have hc : cursor < target.length := Nat.lt_of_not_ge hdone
  have advance (next : State source target spills) (hi : next.invariant (cursor + 1))
      (hb : liveBudget (cursor + 1) next ≤ liveBudget cursor state) :
      Spec (buildBottomUp.loop (cursor + 1) next)
        (fun result => result.2.swapCount ≤ liveBudget cursor state) :=
    (loop_live_bound (cursor + 1) next hi).mono fun _ h => h.trans hb
  have retry (next : State source target spills) (hi : next.invariant cursor)
      (hlt : next.pending_generations < state.pending_generations)
      (hb : liveBudget cursor next ≤ liveBudget cursor state) :
      Spec (buildBottomUp.loop cursor next)
        (fun result => result.2.swapCount ≤ liveBudget cursor state) :=
    (loop_live_bound cursor next hi).mono fun _ h => h.trans hb
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact advance _ (inv.advance hfinal) (liveBudget_advance cursor state)
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
      have hb := permute_le_live inv hc hp.1 hp.2 hperm
      rw [swapCount_concat]
      unfold liveBudget
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
    apply (generate_budget_contract state u hb (inv.available u)).attach.bind
    intro next ⟨hgen, hsw⟩
    exact retry _ (hgen.invariant inv) (hgen.decreases inv)
      (liveBudget_generation inv hb hgen hsw)
  rw [dite_eq_right hurg]
  apply Spec.ite_index (fun hA => hA.2.2)
  · intro _ hB
    let top : Fin target.length := ⟨state.stack.length, by omega⟩
    have hb : state.mapping.symm top = none := by
      simpa [State.positionOf, top] using hB.1
    apply (generate_budget_contract state top hb (inv.available top)).attach.bind
    intro next ⟨hgen, hsw⟩
    exact retry _ (hgen.invariant inv) (hgen.decreases inv)
      (liveBudget_generation inv hb hgen hsw)
  rw [index_eq dest, except_ok_bind]
  rcases Option.eq_none_or_eq_some (state.positionOf dest) with hpos | ⟨carrier, hpos⟩
  · simp only [hpos]
    have hb : state.mapping.symm dest = none := hpos
    apply (generate_budget_contract state dest hb (inv.available dest)).bind
    intro next ⟨hgen, hsw⟩
    have hp := hgen.placement inv
    have hcost : liveBudget cursor next ≤ liveBudget cursor state :=
      liveBudget_generation inv hb hgen hsw
    let current : Fin next.stack.length := ⟨cursor, hp.in_bounds⟩
    rw [index_eq current, except_ok_bind]
    by_cases hf : ∃ h, next.isFinal ⟨cursor, h⟩
    · rw [ite_eq_left ((next.isFinal_iff current).mpr hf)]
      exact advance _ (hp.toInvariant.advance hf) ((liveBudget_advance cursor next).trans hcost)
    · rw [ite_eq_right ((next.isFinal_iff current).not.mpr hf)]
      finish_live cursor, next, hp, hf, Nat.le_succ_of_le hcost, (fun _ => hcost), advance
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
      · exact (liveBudget_advance _ _).trans
          (liveBudget_retag state current carrier (fun hf => hnfinal ⟨_, hf⟩) hcarrier)
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
    by_cases hplaced : pos.val = cursor
    · simp only [hplaced, ↓reduceIte]
      exact advance _ (hi.advance
        ((retag.isFinal_of_bound_iff dest pos hd).mpr hplaced))
        ((liveBudget_advance _ _).trans hretag)
    simp only [hplaced, ↓reduceIte]
    by_cases hnotTop : pos.val ≠ retag.stack.length - 1
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
      rw [index_eq (size := retag.stack.length) pos]
      simp only [except_ok_bind]
      have hbelow := Stack.belowOfNotTop retag.stack pos hnotTop
      by_cases hr : retag.isSwapReachable pos
      · rw [ite_eq_right (not_not_intro hr)]
        apply (invariant_swap_bound_live (dest := dest) cursor hi pos hd hbelow hr hplaced).bind
        rintro next ⟨hp, hlen, hbud⟩
        have hcost : liveBudget cursor next ≤ liveBudget cursor state + 1 := by
          omega
        have htopcost : cursor = next.stack.length - 1 →
            liveBudget cursor next ≤ liveBudget cursor state := by
          intro htop
          have := pos.isLt
          dsimp [retag] at hlen
          omega
        finish_live cursor, next, hp.1, hp.2, hcost, htopcost, advance
      · rw [ite_eq_left hr]
        exact True.intro
    · dsimp +zetaDelta only at hnotTop
      simp only [ne_eq, hnotTop, ↓reduceIte]
      have hp := hi.bound_at_top (dest := dest) pos hd (not_not.mp hnotTop) hplaced
      finish_live cursor, retag, hp.1, hp.2, Nat.le_succ_of_le hretag, (fun _ => hretag), advance
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

end Shuffler.Optimality.BBU
