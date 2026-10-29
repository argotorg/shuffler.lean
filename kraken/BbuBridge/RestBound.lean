import BbuBridge.Statements

/-!
The branch of the loop for a bound offset: `Bbu.takeBound` and `Bbu.placeTop`.

`rbBound`, `rbAfter` and `rbTail` are copies of the parts of `origRest`, so
that `origRest` is `rbBound` by `rfl` after the first branches are removed.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

variable {source target : Stack} {spills : SpillSet}
-- The end of the loop body: swap the top down into `t`.
def rbTail (targetOffset : Nat) (state : State source target spills) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do
  let mut state := state
  _ ← requires (¬ state.isFinal (← index state.stack.length targetOffset)) "target slot is already final"
  if targetOffset ≠ state.stack.length - 1 then
    if ¬ (state.isSwapReachable (← index state.stack.length targetOffset)) then
      throw (← state.blockSwapUnreachable (← index state.stack.length targetOffset))
    state ← state.swapWith targetOffset
  return ← buildBottomUp.loop (targetOffset + 1) state

-- The rest of the bound branch, once the copy at `pos` is chosen.
def rbAfter (targetOffset : Nat) (state : State source target spills) (b pos : Nat) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do
  _ ← requires ((← slotAt state.stack pos) = (← slotAt state.stack b))
    "selected copy differs from the bound slot"
  let state ← state.swapDestinations pos b
  if pos = targetOffset then
    return ← buildBottomUp.loop (targetOffset + 1) state
  if pos ≠ state.stack.length - 1 then
    if ¬ (state.isSwapReachable (← index state.stack.length pos)) then
      throw (← state.blockSwapUnreachable (← index state.stack.length pos))
    let state ← state.swapWith pos
    return ← rbTail targetOffset state
  rbTail targetOffset state

-- The branch for the slot at `bound` bound for `targetOffset`.
def rbBound (targetOffset : Nat) (state : State source target spills)
    (bound : Fin state.stack.length) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do
  _ ← requires (bound ≥ targetOffset) "slot bound for the offset being filled is missing or already below it"
  if (← slotAt state.stack targetOffset) = (← slotAt state.stack bound) then
    rbAfter targetOffset state bound targetOffset
  else
    origCopyScan state bound >>= rbAfter targetOffset state bound

-- `origRest` is `rbBound` when the first two branches are not taken.
theorem rb_origRest (t : Nat) (state : State source target spills) (uo : Option Nat)
    (htn : t < target.length) (bb : Fin state.stack.length)
    (h1 : ¬ (uo.isSome ∧ uo ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH))
    (h2 : ¬ (uo.isNone ∧ state.stack.length > t ∧ state.stack.length < target.length ∧
      (∃ hl : state.stack.length < target.length, (state.positionOf ⟨_, hl⟩).isNone) ∧
      state.stack.length - t < MAX_SWAP_DEPTH))
    (hpos : state.positionOf ⟨t, htn⟩ = some bb) :
    origRest t state uo = rbBound t state bb := by
  unfold origRest
  dsimp only
  rw [dite_eq_right h1]
  by_cases h3 : uo.isNone = true ∧ state.stack.length > t ∧ state.stack.length < target.length
  on_goal 1 =>
    rw [ite_eq_left h3, show index target.length state.stack.length = .ok ⟨_, h3.2.2⟩ from
      index_eq ⟨_, h3.2.2⟩, except_ok_bind,
      ite_eq_right (fun h4 => h2 ⟨h3.1, h3.2.1, h3.2.2, ⟨h3.2.2, h4.1⟩, h4.2⟩)]
  on_goal 2 => rw [ite_eq_right h3]
  all_goals
    rw [show index target.length t = .ok ⟨t, htn⟩ from index_eq ⟨t, htn⟩, except_ok_bind, hpos]
    unfold rbBound origCopyScan
    dsimp only
    rw [bind_pure, index_eq bb, except_ok_bind]
    rfl

variable {e : Bbu.Env} {src : Stack}

-- A failed check.
theorem rb_requires_false {c : Prop} [Decidable c] (h : ¬ c) (r : String) :
    requires c r = .error (.assertion r) := by
  simp [requires, h]; rfl

-- The error of a swap that does not reach `p`.
theorem rb_blockSwap (state : State source target spills)
    (p : Fin state.stack.length) (hr : MAX_SWAP_DEPTH < state.stack.length - 1 - p) :
    state.blockSwapUnreachable p = .ok (.Blocked ⟨p, state.stack.length - 1 - p - MAX_SWAP_DEPTH⟩) := by
  unfold State.blockSwapUnreachable State.block
  rw [requires_of_true _ (by simp only [State.depthOf, Stack.offsetToDepth]; omega)]
  rfl

-- `Bbu.placeTop` is `rbTail`. The state `state0` is any state: `placeTop` never ends the loop.
theorem rb_placeTop (hswap : SwapWithStmt) (st : Bbu.St) (state0 state : OState e src) (t : Nat)
    (h : Rel e st state) : StepCorr e (Bbu.placeTop st t) state0 (rbTail t state) := by
  unfold Bbu.placeTop rbTail
  dsimp only
  by_cases hl : t < st.len
  · have hl' : t < state.stack.length := h.len ▸ hl
    rw [show index state.stack.length t = .ok ⟨t, hl'⟩ from index_eq ⟨t, hl'⟩, except_ok_bind]
    by_cases hf : st.dest t = t
    · rw [ite_eq_left (Or.inr hf)]
      have hf' : state.isFinal ⟨t, hl'⟩ := (h.isFinal ⟨t, hl'⟩).mpr hf
      exact ⟨_, by rw [rb_requires_false (not_not_intro hf')]; rfl, rfl⟩
    have hf' : ¬ state.isFinal ⟨t, hl'⟩ := fun h' => hf ((h.isFinal ⟨t, hl'⟩).mp h')
    rw [ite_eq_right (by omega), requires_of_true _ hf', except_ok_bind]
    have hl2 : state.stack.length = st.len := h.len
    by_cases ht : t = st.len - 1
    · rw [ite_eq_right (show ¬ t ≠ st.len - 1 by omega),
        ite_eq_right (show ¬ t ≠ state.stack.length - 1 by omega)]
      exact ⟨state, h, rfl⟩
    rw [ite_eq_left ht, ite_eq_left (show t ≠ state.stack.length - 1 by omega), except_ok_bind]
    by_cases hr : Bbu.MAX_SWAP_DEPTH < st.len - 1 - t
    · rw [ite_eq_left hr]
      have hr' : ¬ state.isSwapReachable ⟨t, hl'⟩ := by
        simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, MAX_SWAP_DEPTH]
        simp only [Bbu.MAX_SWAP_DEPTH] at hr
        omega
      rw [ite_eq_left hr']
      rw [except_ok_bind, rb_blockSwap _ _ (by simp only [MAX_SWAP_DEPTH, Bbu.MAX_SWAP_DEPTH] at hr ⊢; omega),
        except_ok_bind]
      exact ⟨_, rfl, by simp [encodeErr, hl2]; rfl⟩
    rw [ite_eq_right hr]
    have hr' : state.isSwapReachable ⟨t, hl'⟩ := by
      simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, MAX_SWAP_DEPTH]
      simp only [Bbu.MAX_SWAP_DEPTH] at hr
      omega
    rw [ite_eq_right (not_not_intro hr')]
    have hc := hswap e src st state t h
    cases hm : Bbu.swapWith st t <;> cases ho : state.swapWith t <;> rw [hm, ho] at hc <;>
      simp only [Corr] at hc
    · exact ⟨_, rfl, hc⟩
    · exact ⟨_, hc, rfl⟩
  · rw [ite_eq_left (Or.inl (by omega))]
    have hl' : ¬ t < state.stack.length := by rw [h.len]; exact hl
    exact ⟨_, by simp [index, hl']; rfl, rfl⟩

-- The model after the copy at `pos` is chosen: `Bbu.takeBound` and `Bbu.placeTop`.
def rbAfterM (st : Bbu.St) (t b pos : Nat) : Bbu.M (Bbu.St × Bbu.Next) :=
  (let st := Bbu.swapDestinations st pos b
   if pos = t then .ok (st, true)
   else if pos ≠ st.len - 1 then
     let depth := st.len - 1 - pos
     if Bbu.MAX_SWAP_DEPTH < depth then .error (.blocked pos (depth - Bbu.MAX_SWAP_DEPTH))
     else (Bbu.swapWith st pos).map (·, false)
   else .ok (st, false)).bind fun (st, done) =>
    if done then .ok (st, .next (t + 1)) else Bbu.placeTop st t

-- The rest of the branch for the chosen copy at `pos`.
theorem rb_after (hdest : SwapDestStmt) (hswap : SwapWithStmt) (st : Bbu.St) (state : OState e src)
    (t b pos : Nat) (h : Rel e st state) (hb : b < st.len) (hp : pos < st.len)
    (hv : st.val pos = st.val b) : StepCorr e (rbAfterM st t b pos) state (rbAfter t state b pos) := by
  have hb' : b < state.stack.length := h.len ▸ hb
  have hp' : pos < state.stack.length := h.len ▸ hp
  unfold rbAfterM rbAfter
  dsimp only
  rw [show slotAt state.stack pos = .ok state.stack[pos] from slotAt_index _ ⟨pos, hp'⟩,
    show slotAt state.stack b = .ok state.stack[b] from slotAt_index _ ⟨b, hb'⟩, except_ok_bind,
    except_ok_bind, requires_of_true _ (by rw [show state.stack[pos] = _ from h.get ⟨pos, hp'⟩,
      show state.stack[b] = _ from h.get ⟨b, hb'⟩, hv]),
    except_ok_bind]
  obtain ⟨state', hs, hr⟩ := hdest e src st state pos b h hp hb
  rw [hs, except_ok_bind]
  have hl : (Bbu.swapDestinations st pos b).len = st.len := (Bbu.swapDest_shape st pos b).1
  have hl2 : state'.stack.length = st.len := hr.len.trans hl
  have hp2 : pos < state'.stack.length := by omega
  by_cases hpt : pos = t
  · rw [ite_eq_left hpt, ite_eq_left hpt]
    exact ⟨state', hr, rfl⟩
  rw [ite_eq_right hpt, ite_eq_right hpt]
  by_cases htop : pos = st.len - 1
  · rw [ite_eq_right (show ¬ pos ≠ (Bbu.swapDestinations st pos b).len - 1 by omega),
      ite_eq_right (show ¬ pos ≠ state'.stack.length - 1 by omega)]
    exact rb_placeTop hswap _ state _ t hr
  rw [ite_eq_left (show pos ≠ (Bbu.swapDestinations st pos b).len - 1 by omega),
    ite_eq_left (show pos ≠ state'.stack.length - 1 by omega),
    show index state'.stack.length pos = .ok ⟨pos, hp2⟩ from index_eq ⟨pos, hp2⟩, except_ok_bind]
  by_cases hd : Bbu.MAX_SWAP_DEPTH < (Bbu.swapDestinations st pos b).len - 1 - pos
  · rw [ite_eq_left hd]
    have hd' : ¬ state'.isSwapReachable ⟨pos, hp2⟩ := by
      simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, MAX_SWAP_DEPTH]
      simp only [Bbu.MAX_SWAP_DEPTH] at hd
      omega
    rw [ite_eq_left hd', except_ok_bind,
      rb_blockSwap _ _ (by simp only [MAX_SWAP_DEPTH, Bbu.MAX_SWAP_DEPTH] at hd ⊢; omega), except_ok_bind]
    exact ⟨_, rfl, by simp [encodeErr, hl, hl2]; rfl⟩
  rw [ite_eq_right hd]
  have hd' : state'.isSwapReachable ⟨pos, hp2⟩ := by
    simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, MAX_SWAP_DEPTH]
    simp only [Bbu.MAX_SWAP_DEPTH] at hd
    omega
  rw [ite_eq_right (not_not_intro hd')]
  have hc := hswap e src _ state' pos hr
  cases hm : Bbu.swapWith (Bbu.swapDestinations st pos b) pos <;> cases ho : state'.swapWith pos <;>
    rw [hm, ho] at hc <;> simp only [Corr] at hc
  · exact ⟨_, rfl, hc⟩
  · exact rb_placeTop hswap _ state _ t hc

-- The copy that `Bbu.movableCopy` finds holds the same value.
theorem rb_movableCopy (st : Bbu.St) (b : Nat) (hb : b < st.len) :
    (Bbu.movableCopy st b).getD b < st.len ∧ st.val ((Bbu.movableCopy st b).getD b) = st.val b := by
  cases hm : Bbu.movableCopy st b with
  | none => exact ⟨hb, rfl⟩
  | some c =>
    refine ⟨Bbu.movableCopy_lt hm, ?_⟩
    have := List.find?_some hm
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1

theorem restBound_corr (hcopy : CopyScanStmt) (hdest : SwapDestStmt) (hswap : SwapWithStmt) :
    RestBoundStmt := by
  intro e source st state t u uo b h ht hu c4 c5 hb
  have htn : t < (tgt e).length := by rw [tgt_length]; exact ht
  have hl := h.len
  have hbl : b < st.len := Bbu.positionOf_some h.pos hb
  have hbs : b < state.stack.length := by omega
  have hpos : state.positionOf ⟨t, htn⟩ = some ⟨b, hbs⟩ := by
    have := h.positionOf ⟨t, htn⟩
    rw [hb] at this
    obtain ⟨k, hk, hkb⟩ := Option.map_eq_some_iff.mp this
    rw [hk, show k = ⟨b, hbs⟩ from Fin.ext hkb]
  -- The first two branches of `origRest` are not taken.
  have h1 : ¬ (uo.isSome ∧ uo ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) := by
    rintro ⟨hs, hne, hlt⟩
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hx, rfl⟩ := hu
    exact c4 ⟨by omega, fun hxt => hne (by rw [hxt]),
      by simp only [MAX_SWAP_DEPTH, Bbu.MAX_SWAP_DEPTH] at hlt ⊢; omega⟩
  have h2 : ¬ (uo.isNone ∧ state.stack.length > t ∧ state.stack.length < (tgt e).length ∧
      (∃ hl : state.stack.length < (tgt e).length, (state.positionOf ⟨_, hl⟩).isNone) ∧
      state.stack.length - t < MAX_SWAP_DEPTH) := by
    rintro ⟨hn, hgt, hlt, ⟨hl', hp⟩, hd⟩
    rw [Option.isNone_iff_eq_none] at hn hp
    subst hn
    have := h.positionOf ⟨_, hl'⟩
    rw [hp, Option.map_none] at this
    rw [tgt_length] at hlt
    exact c5 ⟨hu, by omega, by omega, by rw [← hl]; exact this.symm,
      by simp only [MAX_SWAP_DEPTH, Bbu.MAX_SWAP_DEPTH] at hd ⊢; omega⟩
  rw [rb_origRest t state uo htn ⟨b, hbs⟩ h1 h2 hpos]
  unfold Bbu.takeBound rbBound
  by_cases hbt : b < t
  · rw [ite_eq_left hbt, rb_requires_false (by simp only [ge_iff_le, not_le]; exact hbt)]
    exact ⟨_, rfl, rfl⟩
  have htl : t < state.stack.length := by omega
  rw [ite_eq_right hbt, requires_of_true _ (by simp only [ge_iff_le, not_lt] at hbt ⊢; exact hbt),
    except_ok_bind, show slotAt state.stack t = .ok state.stack[t] from slotAt_index _ ⟨t, htl⟩,
    show slotAt state.stack b = .ok state.stack[b] from slotAt_index _ ⟨b, hbs⟩, except_ok_bind,
    except_ok_bind]
  have hgt : state.stack[t] = decode (st.val t) := h.get ⟨t, htl⟩
  have hgb : state.stack[b] = decode (st.val b) := h.get ⟨b, hbs⟩
  dsimp only
  by_cases hv : st.val t = st.val b
  · rw [ite_eq_left hv, ite_eq_left (show state.stack[t] = state.stack[b] by rw [hgt, hgb, hv])]
    exact rb_after hdest hswap st state t b t h hbl (by omega) hv
  rw [ite_eq_right hv,
    ite_eq_right (show ¬ state.stack[t] = state.stack[b] by rw [hgt, hgb, decode_eq_iff (h.canonVal _) (h.canonVal _)]; exact hv),
    hcopy e source st state ⟨b, hbs⟩ h, except_ok_bind]
  obtain ⟨hp, hpv⟩ := rb_movableCopy st b hbl
  exact rb_after hdest hswap st state t b _ h hbl hp hpv

end BbuBridge
