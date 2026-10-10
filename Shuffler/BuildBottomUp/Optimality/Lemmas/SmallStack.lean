import Shuffler.BuildBottomUp.Optimality.Defs
import Shuffler.BuildBottomUp.Optimality.Lemmas.GenerationLowerBound
import Shuffler.BuildBottomUp.Optimality.Lemmas.NoGeneration
import Shuffler.BuildBottomUp.Optimality.Lemmas.GeneralBound
import Shuffler.BuildBottomUp.Lemmas.ReachScan

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Shuffler.Optimality.BBU

open Shuffler.BuildBottomUp

-- A generation for `dest`: `mid` holds the produced slot on top. Then either nothing
-- happens, or `dest` and the top exchange values and destinations with at most one SWAP.
def Grows (state next : State source target spills) (dest : Fin target.length) : Prop :=
  ∃ mid : State source target spills, Growth state mid dest (state.pending_generations - 1) ∧
    mid.trace.swapCount = state.trace.swapCount ∧
    (next = mid ∨ ∃ h : dest.val < mid.stack.length, dest.val + 1 < mid.stack.length ∧
      Swapped mid next ⟨dest.val, h⟩ ∧ next.trace.swapCount ≤ mid.trace.swapCount + 1)

theorem generate_grows (state : State source target spills) (dest : Fin target.length)
    (hbound : state.mapping.symm dest = none) (havailable : state.isAvailable dest) :
    ⦃True⦄ state.generate dest.val
    ⦃fun next => Grows state next dest; allowedErrors⦄ := by
  vcgen [State.generate, produce_counted_spec, swapWith_counted_spec]
  all_goals try simp only [Fin.val_inj] at *
  all_goals subst_vars
  all_goals first
    | exact Fin.isLt _
    | assumption
    | omega
    | exact (by assumption : _ ∧ _).2
    | exact ⟨_, (by assumption : _ ∧ _).1, (by assumption : _ ∧ _).2, Or.inl rfl⟩
    | (simp only [State.isSwapReachable, State.depthOf, Stack.isSwapReachable,
        Stack.offsetToDepth] at *; omega)
    | skip
  case vc3 =>
    rename_i _ _ hg _ _ _ hbelow _ heq
    exact ⟨_, hg.1, hg.2, Or.inr ⟨by omega, hbelow, Swapped.retag _ _ heq, by simp⟩⟩
  case vc7 =>
    rename_i _ _ hg _ _ _ _ _ _ hbelow _ _ _ hs
    exact ⟨_, hg.1, hg.2, Or.inr ⟨by omega, hbelow, hs.1, by omega⟩⟩
  case vc10 =>
    rename_i _ mid _ cur hnf _ _ _ _ hcur _ _
    exact State.not_isFinal_of_val_eq hnf hcur

-- The scan selects only urgent offsets.
theorem urgentScan_urgent (cursor : ℕ) (state : State source target spills) :
    ⦃True⦄ (do
      let mut urgent := none
      for offset in [cursor : target.length] do
        if (state.positionOf (← index target.length offset)).isSome then
          continue
        let slot ← slotAt target offset
        if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
          continue
        if let some copy := state.stack.shallowestCopyPosition slot then
          if ¬ state.stack.isDupReachable copy then
            throw (.blocked ((state.depthOf copy) - MAX_DUP_DEPTH))
          if (state.depthOf copy) = MAX_DUP_DEPTH ∧ copy.val ≠ cursor ∧ urgent.isNone then
            urgent := some offset
      return urgent : Except Error (Option ℕ))
    ⦃fun urgent => ∀ offset, urgent = some offset → Urgent cursor state offset; allowedErrors⦄ := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  vcgen [slotAt, index, State.depthOf] invariants
  · fun _ _ urgent => ∀ offset, urgent = some offset → Urgent cursor state offset
  all_goals try simp_all [allowedErrors]
  case vc6 =>
    rename_i _ cur _ _ hlt _ copy _ hnone hgen hcopy _ hdepth
    exact ⟨hlt, hnone, hgen.2.1, hgen.2.2, copy, hcopy, hdepth.1, hdepth.2.1⟩
  case vc10 => exact (not_lt_of_ge (by assumption)) (range_offset_lt (by assumption))

--- The invariant ----------------------------------------------------------------------------------

-- A PUSH or a load produces a loose value without a copy.
def Loose (spills : SpillSet) (value : Value) : Prop :=
  value.can_be_freely_generated ∨ spills.is_spilled value

-- An open position is on the stack and does not hold its destination.
def Opened (state : State source target spills) (p : ℕ) : Prop :=
  p < state.stack.length ∧ ¬ ∃ h, state.isFinal ⟨p, h⟩

-- The SWAPs that move a value at p to N - 1 in hops of at most 16 positions.
def hops (N p : ℕ) : ℕ := (N - 1 - p + 15) / 16

-- Every stack value is `value` or loose. At most one position is open. An open
-- position, or else a copy of a pinned `value`, has a SWAP budget inside `bound`.
structure Small (value : Value) (bound cursor : ℕ) (state : State source target spills) : Prop where
  values : ∀ x ∈ state.stack, x = value ∨ Loose spills x
  single : ∀ p q, Opened state p → Opened state q → p = q
  width : state.stack.length ≤ cursor + 16
  swaps : state.trace.swapCount ≤ bound
  carrier : ∀ p, Opened state p → state.trace.swapCount + hops target.length p ≤ bound ∧
    (¬ Loose spills value → state.stack[p]? = some value)
  copy : (∀ p, ¬ Opened state p) → ¬ Loose spills value →
    ∃ q, state.stack[q]? = some value ∧ state.trace.swapCount + hops target.length (q + 16) ≤ bound

theorem Small.advance {state : State source target spills} (h : Small value bound cursor state) :
    Small value bound (cursor + 1) state :=
  { h with width := by have := h.width; omega }

theorem isFinal_growth_iff {state mid : State source target spills} {dest : Fin target.length}
    (hg : Growth state mid dest pending) {p : ℕ} (hp : p ≠ dest.val) :
    (∃ h, mid.isFinal ⟨p, h⟩) ↔ ∃ h, state.isFinal ⟨p, h⟩ := by
  rw [State.exists_isFinal_iff, State.exists_isFinal_iff]
  split
  · rename_i hlt
    rw [hg.others ⟨p, hlt⟩ (fun h => hp (congrArg Fin.val h))]
  · rfl

theorem opened_of_bound {state : State source target spills} (dest : Fin target.length)
    (pos : Fin state.stack.length) (hbound : state.mapping.symm dest = some pos)
    (hne : pos.val ≠ dest.val) : Opened state pos.val :=
  ⟨pos.isLt, fun hf => state.boundNotFinal dest pos hbound hne hf.2⟩

-- A target value has a copy on the stack unless it is loose.
theorem Small.target_value {state : State source target spills} (h : Small value bound cursor state)
    (dest : Fin target.length) (havailable : state.isAvailable dest) :
    target[dest] = value ∨ Loose spills target[dest] := by
  rcases havailable with hfree | hspill | hcopy
  · exact Or.inr (Or.inl hfree)
  · exact Or.inr (Or.inr hspill)
  · exact h.values _ ((Stack.shallowestCopyPosition_isSome _ _).mp hcopy)

theorem Small.growth_values {state mid : State source target spills} {dest : Fin target.length}
    (h : Small value bound cursor state) (havailable : state.isAvailable dest)
    (hg : Growth state mid dest pending) : ∀ x ∈ mid.stack, x = value ∨ Loose spills x := by
  intro x hx
  rw [hg.stack_eq, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h.values x hx
  · exact h.target_value dest havailable

-- A generation at the top keeps the open positions and their values.
theorem Small.top {state mid : State source target spills} {dest : Fin target.length}
    (h : Small value bound cursor state) (havailable : state.isAvailable dest)
    (hg : Growth state mid dest pending) (hswaps : mid.trace.swapCount = state.trace.swapCount)
    (hdest : dest.val = state.stack.length) (hwidth : state.stack.length + 1 ≤ cursor + 16) :
    Small value bound cursor mid := by
  have hsize := hg.size
  have hopen : ∀ p, Opened mid p → Opened state p := by
    rintro p ⟨hp, hnf⟩
    have hne : p ≠ dest.val := by
      intro heq
      subst heq
      exact hnf ((mid.isFinal_of_bound_val_iff dest _ hg.bound).mpr hdest.symm)
    by_cases hlt : p < state.stack.length
    · exact ⟨hlt, (isFinal_growth_iff hg hne).not.mp hnf⟩
    · exact (hne (by omega)).elim
  have hget : ∀ p, p < state.stack.length → mid.stack[p]? = state.stack[p]? := by
    intro p hp
    rw [hg.stack_eq, List.getElem?_append_left hp]
  refine ⟨h.growth_values havailable hg, fun p q hp hq => h.single p q (hopen p hp) (hopen q hq),
    by omega, hswaps ▸ h.swaps, ?_, ?_⟩
  · intro p hp
    have := h.carrier p (hopen p hp)
    rw [hswaps, hget p (hopen p hp).1]
    exact this
  · intro hnone hpinned
    have hnone' : ∀ p, ¬ Opened state p := by
      intro p hp
      have hlt := hp.1
      refine hnone p ⟨by omega, ?_⟩
      rw [isFinal_growth_iff hg (by omega)]
      exact hp.2
    obtain ⟨q, hq, hcost⟩ := h.copy hnone' hpinned
    have hql : q < state.stack.length := (List.getElem?_eq_some_iff.mp hq).1
    exact ⟨q, (hget q hql).trans hq, hswaps ▸ hcost⟩

-- An urgent target holds the pinned value. Its shallowest copy is 16 positions below the top.
theorem Small.urgent {state : State source target spills} (h : Small value bound cursor state)
    (hu : Urgent cursor state offset) :
    ∃ copy : Fin state.stack.length, state.stack.shallowestCopyPosition value = some copy ∧
      copy.val + 16 = state.stack.length ∧ ¬ Loose spills value ∧
      ∃ hlt : offset < target.length, target[offset] = value ∧ state.positionOf ⟨offset, hlt⟩ = none := by
  obtain ⟨hlt, hnone, hfree, hspill, copy, hcopy, hdepth, _⟩ := hu
  have hmem := (Stack.shallowestCopyPosition_isSome _ _).mp (by rw [hcopy]; rfl)
  have hloose : ¬ Loose spills target[offset] := by rintro (h | h) <;> contradiction
  have hv : target[offset] = value := (h.values _ hmem).resolve_right hloose
  refine ⟨copy, hv ▸ hcopy, ?_, hv ▸ hloose, hlt, hv, hnone⟩
  rw [Stack.offsetToDepth_val] at hdepth
  have := copy.isLt
  unfold MAX_DUP_DEPTH at hdepth
  omega

-- A pinned value at an open position lies at or below its shallowest copy.
theorem Small.opened_le {state : State source target spills} (h : Small value bound cursor state)
    (hpinned : ¬ Loose spills value) {copy : Fin state.stack.length}
    (hcopy : state.stack.shallowestCopyPosition value = some copy) {p : ℕ}
    (hp : Opened state p) : p ≤ copy.val := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp ((h.carrier p hp).2 hpinned)
  exact shallowestCopyPosition_ge state.stack value copy ⟨p, hlt⟩ hcopy heq

theorem Small.urgent_step {state next : State source target spills} (h : Small value bound cursor state)
    (inv : state.invariant cursor) (hu : Urgent cursor state offset)
    (hwidth : state.stack.length - cursor < MAX_SWAP_DEPTH) (dest : Fin target.length)
    (hdest : dest.val = offset) (hg : Grows state next dest) : Small value bound cursor next := by
  obtain ⟨copy, hcopy, hlen, hpinned, hlt, hv, hnone⟩ := h.urgent hu
  unfold MAX_SWAP_DEPTH at hwidth
  have hclosed : ∀ p, ¬ Opened state p := by
    intro p hp
    have := h.opened_le hpinned hcopy hp
    have : cursor ≤ p := inv.not_final_ge ⟨p, hp.1⟩ (fun hf => hp.2 ⟨_, hf⟩)
    omega
  have hb : state.mapping.symm dest = none := by
    subst hdest
    simpa [State.positionOf, hlt] using hnone
  have hge : state.stack.length ≤ dest.val := by
    by_contra hlt'
    exact hclosed dest ⟨by omega, not_isFinal_of_unbound dest hb⟩
  obtain ⟨mid, hgrow, hswaps, hnext⟩ := hg
  have hmid : next = mid := hnext.resolve_right (by
    rintro ⟨_, hbelow, _⟩
    have := hgrow.size
    omega)
  subst hmid
  have havail := inv.available dest
  have hsize := hgrow.size
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · exact h.top havail hgrow hswaps heq.symm (by omega)
  -- The generated value at the top waits for a deeper destination.
  have hval : next.stack[state.stack.length]? = some value := by
    rw [hgrow.stack_eq, List.getElem?_append_right le_rfl]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
    simpa [← hdest] using hv
  have htopen : Opened next state.stack.length := by
    refine ⟨by omega, fun hf => ?_⟩
    have hf' := (isFinal_growth_iff hgrow (by omega)).mp hf
    have : state.stack.length < state.stack.length := hf'.1
    omega
  have hopen : ∀ p, Opened next p → p = state.stack.length := by
    rintro p ⟨hp, hnf⟩
    by_contra hne
    exact hclosed p ⟨by omega, (isFinal_growth_iff hgrow (by omega)).not.mp hnf⟩
  refine ⟨h.growth_values havail hgrow, fun p q hp hq => (hopen p hp).trans (hopen q hq).symm,
    by omega, hswaps ▸ h.swaps, ?_, fun hnone => (hnone _ htopen).elim⟩
  intro p hp
  obtain rfl := hopen p hp
  refine ⟨?_, fun _ => hval⟩
  obtain ⟨q, hq, hcost⟩ := h.copy hclosed hpinned
  obtain ⟨hql, hqv⟩ := List.getElem?_eq_some_iff.mp hq
  have : q ≤ copy.val := shallowestCopyPosition_ge state.stack value copy ⟨q, hql⟩ hcopy hqv
  rw [hswaps]
  unfold hops at *
  omega

-- When the top branch does not run, the open cursor either is 16 positions
-- below the top or has the top as its destination.
theorem Small.stay {state : State source target spills} (h : Small value bound cursor state)
    (hc : cursor < state.stack.length) (hN : state.stack.length < target.length)
    (hopen : Opened state cursor) {urgent : Option ℕ}
    (hu : ∀ offset, urgent = some offset → Urgent cursor state offset)
    (hurg : ¬ (urgent.isSome ∧ urgent ≠ some cursor ∧
      state.stack.length - cursor < MAX_SWAP_DEPTH))
    (htop : ¬ ∃ hA : urgent.isNone ∧ state.stack.length > cursor ∧
      state.stack.length < target.length,
      (state.positionOf ⟨state.stack.length, hA.2.2⟩).isNone ∧
        state.stack.length - cursor < MAX_SWAP_DEPTH) :
    cursor + 16 ≤ state.stack.length ∨
      state.positionOfNat state.stack.length = some cursor := by
  by_contra hn
  rw [not_or, not_le] at hn
  unfold MAX_SWAP_DEPTH at hurg htop
  cases urgent with
  | none =>
    apply htop ⟨⟨rfl, hc, hN⟩, ?_, by omega⟩
    cases hp : state.mapping.symm ⟨state.stack.length, hN⟩ with
    | none => simp [State.positionOf, hp]
    | some pos =>
      have hpos := h.single _ _ (opened_of_bound _ pos hp (by have := pos.isLt; dsimp; omega)) hopen
      exact (hn.2 (by simp [State.positionOfNat, State.positionOf, hN, hp, hpos])).elim
  | some offset =>
    by_cases ho : offset = cursor
    · subst ho
      obtain ⟨copy, hcopy, hlen, hpinned, _⟩ := h.urgent (hu _ rfl)
      have := h.opened_le hpinned hcopy hopen
      omega
    · exact hurg ⟨rfl, by simpa using ho, by omega⟩

-- The open cursor takes its value. The carrier value moves to the top: it lands
-- there, or it waits 16 positions above the cursor after one SWAP.
theorem Small.carrier_step {state mid final : State source target spills}
    {dest : Fin target.length} (h : Small value bound cursor state) (inv : state.invariant cursor)
    (hdest : dest.val = cursor) (hc : cursor < state.stack.length)
    (hb : state.mapping.symm dest = none)
    (hstay : cursor + 16 ≤ state.stack.length ∨
      state.positionOfNat state.stack.length = some cursor)
    (hg : Growth state mid dest (state.pending_generations - 1))
    (hgs : mid.trace.swapCount = state.trace.swapCount)
    (pos : Fin mid.stack.length) (hpos : pos.val = cursor) (hs : Swapped mid final pos)
    (hfs : final.trace.swapCount ≤ mid.trace.swapCount + 1) :
    final.invariant (cursor + 1) ∧ Small value bound (cursor + 1) final := by
  have hsize := hg.size
  have hfsize := hs.size
  have hgen := Growth.generation_swapped hg hb pos (hpos.trans hdest.symm) hs
  have hinv := hgen.invariant inv
  have htop : (mid.mapping.symm dest).map Fin.val = some (mid.stack.length - 1) := by
    rw [hg.bound, hsize]
    rfl
  have hfc : ∃ h, final.isFinal ⟨cursor, h⟩ := hdest ▸ hs.final dest (hpos.trans hdest.symm) htop
  have hN : state.stack.length < target.length := by
    have := hinv.size
    have := hgen.pending
    have := inv.size
    omega
  have hopen : Opened state cursor := ⟨hc, hdest ▸ not_isFinal_of_unbound dest hb⟩
  obtain ⟨hcost, hcv⟩ := h.carrier cursor hopen
  -- Other positions keep their finality.
  have hkeep : ∀ p, p ≠ cursor → p ≠ state.stack.length →
      ((∃ h, final.isFinal ⟨p, h⟩) ↔ ∃ h, state.isFinal ⟨p, h⟩) := by
    intro p hp1 hp2
    rw [isFinal_swapDestinations_iff pos _ hs.mapping (by omega) (by dsimp; omega)]
    exact isFinal_growth_iff hg (by omega)
  have hopenFinal : ∀ p, Opened final p → p = state.stack.length := by
    rintro p ⟨hp, hnf⟩
    by_contra hne
    have hpc : p ≠ cursor := fun heq => hnf (heq ▸ hfc)
    exact hpc (h.single p cursor ⟨by omega, (hkeep p hpc hne).not.mp hnf⟩ hopen)
  have hval : final.stack[state.stack.length]? = state.stack[cursor]? := by
    have htl : mid.stack.length - 1 = state.stack.length := by omega
    have hm : mid.stack[cursor]? = state.stack[cursor]? := by
      rw [hg.stack_eq, List.getElem?_append_left hc]
    rw [hs.stack_eq, htl, hpos, ← hm, List.getElem?_eq_getElem (by simp; omega),
      List.getElem_swap_right_of_lt (by omega), List.getElem?_eq_getElem (by omega)]
  -- A carrier bound to the top lands there.
  have hland : state.positionOfNat state.stack.length = some cursor →
      ∃ h, final.isFinal ⟨state.stack.length, h⟩ := by
    intro hl
    have hm : (mid.mapping.symm ⟨state.stack.length, hN⟩).map Fin.val = some pos.val := by
      rw [hg.others _ (fun heq => by have := congrArg Fin.val heq; dsimp at this; omega), hpos]
      simpa [State.positionOfNat, State.positionOf, hN] using hl
    have hm' := mid.boundOfVal _ pos hm
    simp [State.exists_isFinal_iff, hN, hs.mapping, hm', hsize]
  have hpinned : ¬ Loose spills value → final.stack[state.stack.length]? = some value :=
    fun hp => hval.trans (hcv hp)
  have hstep : final.trace.swapCount ≤ state.trace.swapCount + 1 := by omega
  refine ⟨hinv.advance hfc, ⟨?_, fun p q hp hq => (hopenFinal p hp).trans (hopenFinal q hq).symm,
    by have := h.width; omega, by unfold hops at hcost; omega, ?_, ?_⟩⟩
  · intro x hx
    rw [hs.stack_eq, List.mem_swap] at hx
    exact h.growth_values (inv.available dest) hg x hx
  · intro p hp
    obtain rfl := hopenFinal p hp
    refine ⟨?_, hpinned⟩
    have hfar : cursor + 16 ≤ state.stack.length := hstay.resolve_right (fun hl => hp.2 (hland hl))
    have := h.width
    unfold hops at hcost ⊢
    omega
  · intro _ hp
    refine ⟨_, hpinned hp, ?_⟩
    unfold hops at hcost ⊢
    omega

-- A generation at or above the top emits no SWAP.
theorem Grows.top {state next : State source target spills} {dest : Fin target.length}
    (h : Grows state next dest) (hdest : state.stack.length ≤ dest.val) :
    Growth state next dest (state.pending_generations - 1) ∧
      next.trace.swapCount = state.trace.swapCount := by
  obtain ⟨mid, hg, hswaps, hnext⟩ := h
  obtain rfl : next = mid := hnext.resolve_right (by
    rintro ⟨_, hbelow, _⟩
    have := hg.size
    omega)
  exact ⟨hg, hswaps⟩

--- The loop ---------------------------------------------------------------------------------------

theorem loop_small (cursor : Nat) (state : State source target spills)
    (inv : state.invariant cursor) (sm : Small value bound cursor state) :
    Spec (buildBottomUp.loop cursor state) (fun result => result.2.swapCount ≤ bound) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  by_cases hdone : cursor ≥ target.length
  · simp only [hdone, ↓reduceIte]
    dsimp [Spec, pure, Except.pure]
    exact sm.swaps
  have hc : cursor < target.length := Nat.lt_of_not_ge hdone
  have advance (next : State source target spills) (hi : next.invariant (cursor + 1))
      (hs : Small value bound (cursor + 1) next) :
      Spec (buildBottomUp.loop (cursor + 1) next) (fun result => result.2.swapCount ≤ bound) :=
    loop_small (cursor + 1) next hi hs
  have retry (next : State source target spills) (hi : next.invariant cursor)
      (hs : Small value bound cursor next)
      (hlt : next.pending_generations < state.pending_generations) :
      Spec (buildBottomUp.loop cursor next) (fun result => result.2.swapCount ≤ bound) :=
    loop_small cursor next hi hs
  simp only [hdone, ↓reduceIte]
  obtain hfinal | hnfinal := em (∃ h, state.isFinal ⟨cursor, h⟩)
  · rw [ite_eq_left hfinal.1, index_eq ⟨cursor, hfinal.1⟩, except_ok_bind,
      ite_eq_left hfinal.2]
    exact advance _ (inv.advance hfinal) sm.advance
  let dest : Fin target.length := ⟨cursor, hc⟩
  rw [skip_unless_final (fun hlt hf => hnfinal ⟨hlt, hf⟩)]
  -- The holder of a bound cursor is a second open position.
  have hb : state.mapping.symm dest = none := by
    cases hholder : state.mapping.symm dest with
    | none => rfl
    | some holder =>
      exfalso
      have hne : holder.val ≠ cursor := fun heq =>
        hnfinal ((state.isFinal_of_bound_iff dest holder hholder).mpr heq)
      have hge := inv.processed.bound_ge dest holder hholder le_rfl
      have := holder.isLt
      exact hne (sm.single _ _ (opened_of_bound dest holder hholder hne) ⟨by omega, hnfinal⟩)
  -- With no pending generation, every target is bound.
  have hz : state.pending_generations ≠ 0 := by
    intro hz
    have ht : ∀ j, (state.mapping.symm j).isSome :=
      (Mapping.unmapped_target_slots_eq_zero state.mapping).mp (inv.pending.trans hz)
    simpa [hb] using ht dest
  simp only [hz, ↓reduceIte]
  have hN : state.stack.length < target.length := by have := inv.size; omega
  have hscan := (spec_iff_triple _ _).mpr (urgentScan_urgent cursor state)
  simp only [bind_pure] at hscan
  apply hscan.bind
  intro urgent hu
  by_cases hurg : urgent.isSome ∧ urgent ≠ some cursor ∧ state.stack.length - cursor < MAX_SWAP_DEPTH
  · rw [dite_eq_left hurg]
    have hurgent := hu (urgent.get hurg.1) (Option.some_get hurg.1).symm
    obtain ⟨hlt, hnone, _⟩ := id hurgent
    let u : Fin target.length := ⟨urgent.get hurg.1, hlt⟩
    have hbu : state.mapping.symm u = none := hnone
    apply (Spec.and (generate_contract state u hbu (inv.available u))
      ((spec_iff_triple _ _).mpr (generate_grows state u hbu (inv.available u)))).attach.bind
    intro next ⟨hgen, hgrow⟩
    exact retry _ (hgen.invariant inv) (sm.urgent_step inv hurgent hurg.2.2 u rfl hgrow)
      (hgen.decreases inv)
  rw [dite_eq_right hurg]
  apply ite_index_rest (fun hA => hA.2.2)
  · intro hA hB
    let top : Fin target.length := ⟨state.stack.length, hA.2.2⟩
    have hbt : state.mapping.symm top = none := by
      simpa [State.positionOf, top] using hB.1
    apply (Spec.and (generate_contract state top hbt (inv.available top))
      ((spec_iff_triple _ _).mpr (generate_grows state top hbt (inv.available top)))).attach.bind
    intro next ⟨hgen, hgrow⟩
    obtain ⟨hg, hgs⟩ := hgrow.top le_rfl
    have := hB.2
    unfold MAX_SWAP_DEPTH at this
    exact retry _ (hgen.invariant inv)
      (sm.top (inv.available top) hg hgs rfl (by omega)) (hgen.decreases inv)
  intro hntop
  rw [index_eq dest, except_ok_bind]
  have hpos : state.positionOf dest = none := hb
  simp only [hpos]
  apply (Spec.and (generate_contract state dest hb (inv.available dest))
    ((spec_iff_triple _ _).mpr (generate_grows state dest hb (inv.available dest)))).bind
  rintro next ⟨hgen, hgrow⟩
  have hp := hgen.placement inv
  let current : Fin next.stack.length := ⟨cursor, hp.in_bounds⟩
  rw [index_eq current, except_ok_bind]
  by_cases hcl : cursor < state.stack.length
  · have hopen : Opened state cursor := ⟨hcl, not_isFinal_of_unbound dest hb⟩
    have hstay := sm.stay hcl hN hopen hu hurg hntop
    obtain ⟨mid, hg, hgs, hnext⟩ := hgrow
    rcases hnext with rfl | ⟨hlt, _, hsw, hcount⟩
    · -- The generation left the carrier in place; the loop swaps it.
      have hf : ¬ ∃ h, next.isFinal ⟨cursor, h⟩ := by
        rw [next.isFinal_of_bound_val_iff dest _ hg.bound]
        exact Nat.ne_of_gt hcl
      rw [ite_eq_right ((next.isFinal_iff current).not.mpr hf)]
      simp only [except_ok_bind]
      rw [requires_of_true (¬ next.isFinal current) ((next.isFinal_iff current).not.mpr hf)]
      simp only [except_ok_bind]
      have hsize := hg.size
      have hnotTop : cursor ≠ next.stack.length - 1 := by omega
      simp +zetaDelta only [ne_eq, hnotTop, not_false_eq_true, ↓reduceIte]
      have hbelow : cursor + 1 < next.stack.length := by omega
      by_cases hr : next.isSwapReachable current
      · rw [ite_eq_right (not_not_intro hr)]
        apply ((spec_iff_triple _ _).mpr
          (swapWith_counted_spec next cursor current.isLt hbelow hr (fun h => hf ⟨_, h⟩))).bind
        rintro final ⟨hsw, hcount⟩
        obtain ⟨hi, hs⟩ :=
          sm.carrier_step inv rfl hcl hb hstay hg hgs current rfl hsw (by omega)
        exact advance _ hi hs
      · rw [ite_eq_left hr]
        exact True.intro
    · -- The generation swapped or retagged the carrier.
      obtain ⟨hi, hs⟩ :=
        sm.carrier_step inv rfl hcl hb hstay hg hgs ⟨cursor, hlt⟩ rfl hsw (by omega)
      have hf : ∃ h, next.isFinal ⟨cursor, h⟩ := hi.processed dest (Nat.lt_succ_self _)
      rw [ite_eq_left ((next.isFinal_iff current).mpr hf)]
      exact advance _ hi hs
  · -- The cursor is the top.
    have hcl' : cursor = state.stack.length := by
      have := inv.cursor_le_length hc
      omega
    obtain ⟨hg, hgs⟩ := hgrow.top (by simp [dest, hcl'])
    have hf : ∃ h, next.isFinal ⟨cursor, h⟩ :=
      (next.isFinal_of_bound_val_iff dest _ hg.bound).mpr hcl'.symm
    rw [ite_eq_left ((next.isFinal_iff current).mpr hf)]
    exact advance _ ((hgen.invariant inv).advance hf)
      (sm.top (inv.available dest) hg hgs (hcl' : dest.val = _) (by omega)).advance
termination_by (target.length - cursor, state.pending_generations)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hlt

--- The upper bound --------------------------------------------------------------------------------

-- With one initial value, that value is the carrier. With none, no position is open.
theorem Small.initial (initial : State source target spills) (h : initial.Valid)
    (hn : initial.stack.length ≤ 1) :
    Small (initial.stack.headD .Wildcard)
      (initial.trace.swapCount + smallSwapBound initial.stack.length initial.pending_generations)
      0 initial := by
  have hsize := h.size
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with hz | hone
  · have hnil := List.length_eq_zero_iff.mp hz
    have hclosed : ∀ p, ¬ Opened initial p := fun p hp => by have := hp.1; omega
    refine ⟨fun x hx => by simp [hnil] at hx, fun p _ hp => (hclosed p hp).elim, by omega,
      by omega, fun p hp => (hclosed p hp).elim, fun _ hpinned => ?_⟩
    exact (hpinned (by simp [hnil, Loose, Value.can_be_freely_generated])).elim
  · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hone
    have hhead : initial.stack.headD .Wildcard = a := by simp [ha]
    have hbound : smallSwapBound initial.stack.length initial.pending_generations =
        (initial.pending_generations + 15) / 16 := by simp [smallSwapBound, hone]
    rw [hhead, hbound]
    have hopen : ∀ p, Opened initial p → p = 0 := fun p hp => by have := hp.1; omega
    refine ⟨fun x hx => by simp [ha] at hx; exact Or.inl hx,
      fun p q hp hq => (hopen p hp).trans (hopen q hq).symm, by omega, by omega, ?_, ?_⟩
    · intro p hp
      obtain rfl := hopen p hp
      refine ⟨?_, fun _ => by simp [ha]⟩
      unfold hops
      omega
    · intro _ _
      refine ⟨0, by simp [ha], ?_⟩
      unfold hops
      omega

--- The attaining families -------------------------------------------------------------------------

variable {source target : Stack} {spills : SpillSet}

-- A final cursor leaves the state unchanged.
theorem Placed.skip {state : State source target spills} {len : ℕ} {lab : ℕ → ℕ}
    (hp : Placed len lab state) (t : ℕ) (ht : t < len) (hlab : lab t = t) :
    buildBottomUp.loop t state = buildBottomUp.loop (t + 1) state := by
  have hN : t < target.length := hlab ▸ hp.range t ht
  have hf : ∃ h, state.isFinal ⟨t, h⟩ := (hp.isFinal_iff t ht).mpr hlab
  have hs : t < state.stack.length := hp.length ▸ ht
  rw [buildBottomUp.loop.eq_def]
  simp only [show ¬ t ≥ target.length by omega, ↓reduceIte]
  rw [ite_eq_left hs, index_eq ⟨t, hs⟩, except_ok_bind,
    ite_eq_left ((state.isFinal_iff ⟨t, hs⟩).mpr hf)]

theorem Placed.skips {state : State source target spills} {len : ℕ} {lab : ℕ → ℕ}
    (hp : Placed len lab state) (t : ℕ) :
    ∀ m, t + m ≤ len → (∀ i, t ≤ i → i < t + m → lab i = i) →
      buildBottomUp.loop t state = buildBottomUp.loop (t + m) state := by
  intro m
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm hlab
    rw [ih (by omega) fun i hi hm' => hlab i hi (by omega),
      hp.skip (t + m) (by omega) (hlab _ (by omega) (by omega))]
    rfl

-- At the end of the target, the loop returns the stack and its trace.
theorem loop_finish (state : State source target spills) :
    Succeeds (buildBottomUp.loop target.length state)
      (fun result => result.2.swapCount = state.trace.swapCount) := by
  rw [buildBottomUp.loop.eq_def]
  simp_loop
  simp only [ge_iff_le, le_refl, ↓reduceIte]
  exact ⟨_, rfl, rfl⟩

/-! Family for one source slot: the slot holds the spilled variable k and is bound to target k.
Target j holds the spilled variable j. -/

def oneSource (k : ℕ) : Stack := [.Var ⟨k⟩]

def oneTarget (k : ℕ) : Stack := List.ofFn fun j : Fin (k + 1) => .Var ⟨j.val⟩

def oneSpills (k : ℕ) : SpillSet := (Finset.range (k + 1)).image VarId.mk

@[simp] theorem oneSource_length : (oneSource k).length = 1 := rfl

@[simp] theorem oneTarget_length : (oneTarget k).length = k + 1 := by simp [oneTarget]

@[simp] theorem oneTarget_getElem (j : ℕ) (h : j < (oneTarget k).length) :
    (oneTarget k)[j] = .Var ⟨j⟩ := by
  simp only [oneTarget, List.getElem_ofFn]

theorem one_allSpilled (k : ℕ) : AllSpilled (oneTarget k) (oneSpills k) := by
  intro j
  have := j.isLt
  simp only [oneTarget_length] at this
  rw [Fin.getElem_fin, oneTarget_getElem]
  simp [SpillSet.is_spilled, oneSpills]
  omega

def oneMapping (k : ℕ) : Mapping (oneSource k).length (oneTarget k).length :=
  PEquiv.single ⟨0, by simp⟩ ⟨k, by simp⟩

def oneState (k : ℕ) : State (oneSource k) (oneTarget k) (oneSpills k) where
  planned_mapping := oneMapping k
  stack := oneSource k
  trace := .Lit (oneSource k)
  mapping := oneMapping k
  pending_generations := k

theorem oneMapping_symm (k : ℕ) (j : Fin (oneTarget k).length) :
    (oneMapping k).symm j = if j.val = k then some ⟨0, by simp⟩ else none := by
  unfold oneMapping
  rw [PEquiv.symm_single]
  split_ifs with h
  · obtain rfl : j = ⟨k, by simp⟩ := Fin.ext h
    exact PEquiv.single_apply _ _
  · exact PEquiv.single_apply_of_ne (fun he => h (by rw [← he])) _

theorem one_valid (k : ℕ) : (oneState k).Valid where
  size := by simp [oneState]; omega
  pending := by
    unfold Mapping.unmapped_target_slots
    change (Finset.univ.filter fun j => (oneMapping k).symm j = none).card = k
    simp only [oneMapping_symm, ite_eq_right_iff, reduceCtorEq, imp_false]
    rw [show (Finset.univ.filter fun j : Fin (oneTarget k).length => ¬ j.val = k) =
        Finset.univ.erase ⟨k, by simp⟩ from by ext j; simp [Fin.ext_iff]]
    simp
  available := (one_allSpilled k).available _

theorem one_positionOf (k j : ℕ) :
    (oneState k).positionOfNat j = if j = k then some 0 else none := by
  unfold State.positionOfNat State.positionOf
  split
  · rename_i hj
    change Option.map Fin.val ((oneMapping k).symm ⟨j, hj⟩) = _
    rw [oneMapping_symm]
    split_ifs <;> rfl
  · rename_i hj
    simp only [oneTarget_length] at hj
    simp only [show ¬ j = k by omega, ↓reduceIte]

theorem one_placed (k : ℕ) : Placed 1 (fun i => if i = 0 then k else i) (oneState k) where
  length := rfl
  value i hi := by
    obtain rfl : i = 0 := by omega
    show (oneSource k)[0]? = (oneTarget k)[k]?
    rw [List.getElem?_eq_getElem (by simp : k < (oneTarget k).length), oneTarget_getElem]
    rfl
  slot i hi := by
    obtain rfl : i = 0 := by omega
    simp [one_positionOf]
  expected := by
    apply List.ext_getElem (by simp [State.expectedStack])
    intro j _ hj
    simp only [State.expectedStack, List.getElem_ofFn]
    split
    · rename_i pos hpos
      change (oneMapping k).symm _ = some pos at hpos
      rw [oneMapping_symm] at hpos
      split_ifs at hpos with he
      cases hpos
      simp only at he
      subst he
      simp only [oneTarget_getElem]
      rfl
    · rfl
  pending := by simp [oneState]
  le := by simp

-- Slots below t are final, slot t holds target k, and slots t + 1 to len - 1 hold their
-- own targets. The loop emits one SWAP for each block of 16 cursors from t below k.
theorem one_loop (k t len : ℕ) (state : State (oneSource k) (oneTarget k) (oneSpills k))
    (hp : Placed len (fun i => if i = t then k else i) state) (htl : t < len) (htk : t < k)
    (hlen : len ≤ t + 16) (hlk : len ≤ k) :
    Succeeds (buildBottomUp.loop t state)
      (fun result => result.2.swapCount = state.trace.swapCount + (k - t + 15) / 16) := by
  have hsp := one_allSpilled k
  have hfree : state.positionOfNat len = none ∨ len = k :=
    if h : len = k then Or.inr h
    else Or.inl ((hp.positionOf_none len).mpr fun i hi => by split_ifs <;> omega)
  by_cases hgen : len < t + 16 ∧ len < k
  · have hfree' : state.positionOfNat len = none := hfree.resolve_right (by omega)
    refine hp.gen_step t state (hsp.reachable state) len le_rfl (by simp; omega) hfree'
      (hsp.available state _) htl (by simp; omega) hgen.1
      (fun choice hu => Or.inr ⟨hsp.no_urgent hu, rfl⟩) fun next hg hc => ?_
    have hn := hp.grow hg hfree' (by simp; omega)
    rw [← hc]
    exact one_loop k t (len + 1) next (hn.congr fun i hi => by (try dsimp only); split_ifs <;> omega)
      (by omega) htk (by omega) (by omega)
  · have hstay : t + 16 ≤ len ∨ ((∀ o, ¬Urgent t state o) ∧
        (len < (oneTarget k).length → state.positionOfNat len ≠ none)) := by
      by_cases hw : t + 16 ≤ len
      · exact Or.inl hw
      · refine Or.inr ⟨fun o ⟨ho, _, _, hns, _⟩ => hns (hsp ⟨o, ho⟩), fun _ => ?_⟩
        have hs : state.positionOfNat k = some t := by simpa using hp.slot t htl
        rw [show len = k by omega]
        rw [hs]
        simp
    have hdiff : (oneTarget k)[(fun i => if i = t then k else i) t]? ≠ (oneTarget k)[t]? := by
      rw [show (fun i => if i = t then k else i) t = k by simp]
      rw [List.getElem?_eq_getElem (by simp), List.getElem?_eq_getElem (by simp; omega)]
      simp only [oneTarget_getElem, ne_eq, Option.some.injEq, Value.Var.injEq, VarId.mk.injEq]
      omega
    refine hp.hole_step t state (hsp.reachable state) hstay htl (by omega) (by simp; omega)
      ((hp.positionOf_none t).mpr fun i hi => by split_ifs <;> omega) (hsp.available state _)
      hdiff fun next hn hc => ?_
    have hn' : Placed (len + 1) (fun i => if i = len then k else i) next :=
      hn.congr fun i hi => by split_ifs <;> omega
    rw [hn'.skips (t + 1) (len - t - 1) (by omega) (fun i h1 h2 => by split_ifs <;> omega),
      show t + 1 + (len - t - 1) = len by omega]
    by_cases hk : len = k
    · subst hk
      rw [hn'.skip len (by omega) (by simp)]
      have hf := loop_finish next
      simp only [oneTarget_length] at hf
      apply hf.mono
      intro result hr
      rw [hr, hc]
      omega
    · apply (one_loop k len (len + 1) next hn' (by omega) (by omega) (by omega) (by omega)).mono
      intro result hr
      rw [hr, hc]
      omega
termination_by (k - t, t + 16 - len)

-- With k ≥ 1 pending generations, the family emits (k + 15) / 16 SWAPs.
theorem one_swapCount (k : ℕ) (hk : 1 ≤ k) :
    ∃ result trace, buildBottomUp (oneState k) (one_valid k) = .ok ⟨result, trace⟩ ∧
      trace.swapCount = (oneState k).trace.swapCount + (k + 15) / 16 := by
  obtain ⟨⟨result, trace⟩, hv, hc⟩ :=
    one_loop k 0 1 (oneState k) (one_placed k) (by omega) (by omega) (by omega) hk
  have hspec := loop_spec 0 (oneState k) (State.invariant.initial (one_valid k))
  rw [hv] at hspec
  have hsize : result.length = (oneTarget k).length := by
    simp [show result = _ from hspec, State.expectedStack]
  refine ⟨result, trace, ?_, hc⟩
  unfold buildBottomUp
  rw [hv, except_ok_bind]
  simp only [requires_of_true _ hsize, except_ok_bind]
  rfl

-- No source slot. Target j holds the spilled variable j, and all k + 1 targets are pending.
def zeroState (k : ℕ) : State [] (oneTarget k) (oneSpills k) where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := k + 1

theorem zero_valid (k : ℕ) : (zeroState k).Valid where
  size := by simp [zeroState]
  pending := by
    unfold Mapping.unmapped_target_slots
    rw [Finset.filter_true_of_mem (p := fun j => (zeroState k).mapping.symm j = none) fun j _ => rfl]
    simp [zeroState]
  available := (one_allSpilled k).available _

end Shuffler.Optimality.BBU
