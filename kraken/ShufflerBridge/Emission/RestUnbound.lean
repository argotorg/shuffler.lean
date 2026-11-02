module

public import ShufflerBridge.Emission.Statements
import all ShufflerBridge.Emission.Statements

@[expose] public section

/-!
The branch of the loop for an unbound offset: `FlatShuffler.generate` and `FlatShuffler.placeTop`.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- With `some t`, `origRest` skips the first two branches.
theorem restUnbound_skip {e : FlatShuffler.Env} {source : Stack} (st : FlatShuffler.St) (state : OState e source)
    (t u : Nat) (uo : Option Nat) (h : Rel e st state) (hu : UrgentRel e.n u uo)
    (c4 : ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + FlatShuffler.MAX_SWAP_DEPTH))
    (c5 : ¬(u = e.n ∧ t < st.len ∧ st.len < e.n ∧ FlatShuffler.positionOf st st.len = none ∧
      st.len < t + FlatShuffler.MAX_SWAP_DEPTH)) :
    origRest t state uo = origRest t state (some t) := by
  have hl := h.len
  have hs : ¬((some t).isSome ∧ some t ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) :=
    fun hc => hc.2.1 rfl
  unfold origRest
  rw [dite_eq_right_of_eq_false (eq_false hs)]
  cases uo with
  | some x =>
    obtain ⟨hx, rfl⟩ := hu
    have hc1 : ¬((some u).isSome ∧ some u ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) := by
      rintro ⟨-, hut, hlen⟩
      refine c4 ⟨by omega, fun h' => hut (by rw [h']), ?_⟩
      rw [← hl]; unfold FlatShuffler.MAX_SWAP_DEPTH; unfold MAX_SWAP_DEPTH at hlen; omega
    rw [dite_eq_right_of_eq_false (eq_false hc1)]
    simp only [Option.isNone_some, Bool.false_eq_true, false_and, ite_false]
  | none =>
    have hc1 : ¬((none : Option Nat).isSome ∧ none ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) :=
      fun hc => by simp at hc
    rw [dite_eq_right_of_eq_false (eq_false hc1)]
    by_cases hA : state.stack.length > t ∧ state.stack.length < (decodedTargetStack e).length
    · have hidx : index (decodedTargetStack e).length state.stack.length = .ok ⟨_, hA.2⟩ := index_eq ⟨_, hA.2⟩
      have hc2 : ¬((state.mapping.positionOf ⟨_, hA.2⟩).isNone ∧ state.stack.length - t < MAX_SWAP_DEPTH) := by
        rintro ⟨hn, hlen⟩
        have hp := h.positionOf ⟨_, hA.2⟩
        rw [Option.isNone_iff_eq_none.mp hn, Option.map_none] at hp
        have hlt := hA.2
        rw [tgt_length] at hlt
        refine c5 ⟨hu, by omega, by omega, ?_, ?_⟩
        · rw [← hl]; exact hp.symm
        · rw [← hl]; unfold FlatShuffler.MAX_SWAP_DEPTH; unfold MAX_SWAP_DEPTH at hlen; omega
      simp only [Option.isNone_none, Option.isNone_some, true_and, hA, Bool.false_eq_true, false_and,
        ite_false, ite_true, hidx, except_ok_bind, hc2]
    · simp only [Option.isNone_none, Option.isNone_some, true_and, hA, Bool.false_eq_true, false_and,
        ite_false]

/-! ## The end of the loop body: `FlatShuffler.placeTop` -/

-- The end of the loop body, as in `origRest` (so it is defeq to the join point there).
def ruTail {source target : Stack} {spills : SpillSet} (targetOffset : Nat)
    (state : State source target spills) :
    Except ShuffleErr (Result source target spills) := do
  let mut state := state
  _ ← requires (¬ state.isFinal (← index state.stack.length targetOffset)) "target slot is already final"
  if targetOffset ≠ state.stack.length - 1 then
    if ¬ (state.isSwapReachable (← index state.stack.length targetOffset)) then
      return ← state.blockSwapUnreachable (← index state.stack.length targetOffset)
    state ← state.swapWith targetOffset
  return ← buildBottomUp.loop (targetOffset + 1) state

theorem ru_requires_false {c : Prop} [Decidable c] (h : ¬ c) (r : String) :
    requires c r = .error (.assertion r) := by
  simp [requires, h]; rfl

theorem ru_blockSwap {source target : Stack} {spills : SpillSet} (state : State source target spills)
    (p : Fin state.stack.length) (hr : MAX_SWAP_DEPTH < state.stack.length - 1 - p) :
    state.blockSwapUnreachable p = .ok ⟨some ⟨p, state.stack.length - 1 - p - MAX_SWAP_DEPTH⟩, state⟩ := by
  unfold State.blockSwapUnreachable State.block
  rw [requires_of_true _ (by simp only [State.depthOf, Stack.offsetToDepth]; omega)]
  rfl

-- `placeTop` is the end of the loop body. The result never is `.finish`, so any
-- `state0` does.
theorem ru_placeTop (hswap : SwapWithStmt) {e : FlatShuffler.Env} {src : Stack} (st : FlatShuffler.St)
    (state state0 : OState e src) (t : Nat) (h : Rel e st state) :
    StepCorr e (FlatShuffler.placeTop st t) state0 (ruTail t state) := by
  unfold FlatShuffler.placeTop ruTail
  dsimp only
  by_cases hl : t < st.len
  · have hl' : t < state.stack.length := h.len ▸ hl
    rw [show index state.stack.length t = .ok ⟨t, hl'⟩ from index_eq ⟨t, hl'⟩, except_ok_bind]
    by_cases hf : st.dest t = t
    · rw [ite_eq_left (Or.inr hf)]
      have hf' : state.isFinal ⟨t, hl'⟩ := (h.isFinal ⟨t, hl'⟩).mpr hf
      exact ⟨_, by rw [ru_requires_false (not_not_intro hf')]; rfl⟩
    have hf' : ¬ state.isFinal ⟨t, hl'⟩ := fun h' => hf ((h.isFinal ⟨t, hl'⟩).mp h')
    rw [ite_eq_right (by omega), requires_of_true _ hf', except_ok_bind]
    have hl2 : state.stack.length = st.len := h.len
    by_cases ht : t = st.len - 1
    · rw [ite_eq_right (show ¬ t ≠ st.len - 1 by omega),
        ite_eq_right (show ¬ t ≠ state.stack.length - 1 by omega)]
      exact ⟨state, h, rfl⟩
    rw [ite_eq_left ht, ite_eq_left (show t ≠ state.stack.length - 1 by omega), except_ok_bind]
    by_cases hr : FlatShuffler.MAX_SWAP_DEPTH < st.len - 1 - t
    · rw [ite_eq_left hr]
      have hr' : ¬ state.isSwapReachable ⟨t, hl'⟩ := by
        simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, MAX_SWAP_DEPTH]
        simp only [FlatShuffler.MAX_SWAP_DEPTH] at hr
        omega
      rw [ite_eq_left hr']
      rw [except_ok_bind, ru_blockSwap _ _ (by simp only [MAX_SWAP_DEPTH, FlatShuffler.MAX_SWAP_DEPTH] at hr ⊢; omega)]
      refine ⟨state, h, ?_⟩
      simp [hl2]; rfl
    rw [ite_eq_right hr]
    have hr' : state.isSwapReachable ⟨t, hl'⟩ := by
      simp only [State.isSwapReachable, State.depthOf, Stack.offsetToDepth, MAX_SWAP_DEPTH]
      simp only [FlatShuffler.MAX_SWAP_DEPTH] at hr
      omega
    rw [ite_eq_right (not_not_intro hr')]
    exact stepcorr_next (t + 1) (hswap e src st state t h)
  · rw [ite_eq_left (Or.inl (by omega))]
    have hl' : ¬ t < state.stack.length := by rw [h.len]; exact hl
    exact ⟨_, by simp [index, hl']; rfl⟩

/-! ## The branch -/

theorem restUnbound_corr (hgen : GenerateStmt) (hswap : SwapWithStmt) : RestUnboundStmt := by
  intro e source st state t u uo h hp0 ht hu c4 c5 hpt
  rw [restUnbound_skip st state t u uo h hu c4 c5]
  have htt : t < (decodedTargetStack e).length := by rw [tgt_length]; exact ht
  have hpt' : state.mapping.positionOf ⟨t, htt⟩ = none := by
    have := h.positionOf ⟨t, htt⟩
    rw [hpt, Option.map_eq_none_iff] at this
    exact this
  have hs : ¬((some t).isSome ∧ some t ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) :=
    fun hc => hc.2.1 rfl
  have hidx : index (decodedTargetStack e).length t = .ok ⟨t, htt⟩ := index_eq ⟨t, htt⟩
  unfold origRest
  rw [dite_eq_right_of_eq_false (eq_false hs)]
  simp only [Option.isNone_some, Bool.false_eq_true, false_and, ite_false, hidx, except_ok_bind, hpt']
  show StepCorr e _ state (state.generate t >>= fun r =>
    if r.blocked.isSome then pure r else
    index r.state.stack.length t >>= fun i =>
      if r.state.isFinal i then buildBottomUp.loop (t + 1) r.state else ruTail t r.state)
  have hg := hgen e source st state t h hp0
  -- Done: as `FlatShuffler.placeTop`.
  refine stepcorr_bind hg fun st' r _ hg => ?_
  generalize r.state = s at hg ⊢
  show StepCorr e (if t < st'.len ∧ st'.dest t = t then _ else _) state _
  by_cases hl : t < st'.len
  · have hl' : t < s.stack.length := hg.len ▸ hl
    rw [index_eq ⟨t, hl'⟩, except_ok_bind]
    by_cases hf : st'.dest t = t
    · rw [ite_eq_left ⟨hl, hf⟩, ite_eq_left ((hg.isFinal ⟨t, hl'⟩).mpr hf)]
      exact ⟨s, hg, rfl⟩
    · rw [ite_eq_right (fun h' => hf h'.2),
        ite_eq_right (fun h' => hf ((hg.isFinal ⟨t, hl'⟩).mp h'))]
      exact ru_placeTop hswap st' s state t hg
  · have hl' : ¬ t < s.stack.length := by rw [hg.len]; exact hl
    rw [ite_eq_right (fun h' => hl h'.1)]
    unfold FlatShuffler.placeTop
    rw [ite_eq_left (Or.inl (by omega))]
    exact ⟨_, by simp [index, hl']; rfl⟩

end ShufflerBridge.Emission
