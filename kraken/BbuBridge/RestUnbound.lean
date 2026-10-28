import BbuBridge.Statements

/-!
The branch of the loop for an unbound offset: `Bbu.generate` and `Bbu.placeTop`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- With `some t`, `origRest` skips the first two branches.
theorem restUnbound_skip {e : Bbu.Env} {source : Stack} (st : Bbu.St) (state : OState e source)
    (t u : Nat) (uo : Option Nat) (h : Rel e st state) (hu : UrgentRel e.n u uo)
    (c4 : ¬(u ≠ e.n ∧ u ≠ t ∧ st.len < t + Bbu.MAX_SWAP_DEPTH))
    (c5 : ¬(u = e.n ∧ t < st.len ∧ st.len < e.n ∧ Bbu.positionOf st st.len = none ∧
      st.len < t + Bbu.MAX_SWAP_DEPTH)) :
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
      rw [← hl]; unfold Bbu.MAX_SWAP_DEPTH; unfold MAX_SWAP_DEPTH at hlen; omega
    rw [dite_eq_right_of_eq_false (eq_false hc1)]
    simp only [Option.isNone_some, Bool.false_eq_true, false_and, ite_false]
  | none =>
    have hc1 : ¬((none : Option Nat).isSome ∧ none ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) :=
      fun hc => by simp at hc
    rw [dite_eq_right_of_eq_false (eq_false hc1)]
    by_cases hA : state.stack.length > t ∧ state.stack.length < (tgt e).length
    · have hidx : index (tgt e).length state.stack.length = .ok ⟨_, hA.2⟩ := index_eq ⟨_, hA.2⟩
      have hc2 : ¬((state.positionOf ⟨_, hA.2⟩).isNone ∧ state.stack.length - t < MAX_SWAP_DEPTH) := by
        rintro ⟨hn, hlen⟩
        have hp := h.positionOf ⟨_, hA.2⟩
        rw [Option.isNone_iff_eq_none.mp hn, Option.map_none] at hp
        have hlt := hA.2
        rw [tgt_length] at hlt
        refine c5 ⟨hu, by omega, by omega, ?_, ?_⟩
        · rw [← hl]; exact hp.symm
        · rw [← hl]; unfold Bbu.MAX_SWAP_DEPTH; unfold MAX_SWAP_DEPTH at hlen; omega
      simp only [Option.isNone_none, Option.isNone_some, true_and, hA, Bool.false_eq_true, false_and,
        ite_false, ite_true, hidx, except_ok_bind, hc2]
    · simp only [Option.isNone_none, Option.isNone_some, true_and, hA, Bool.false_eq_true, false_and,
        ite_false]

/-! ## The end of the loop body: `Bbu.placeTop` -/

-- The end of the loop body, as in `origRest` (so it is defeq to the join point there).
def ruTail {source target : Stack} {spills : SpillSet} (targetOffset : Nat)
    (state : State source target spills) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do
  let mut state := state
  _ ← requires (¬ state.isFinal (← index state.stack.length targetOffset)) "target slot is already final"
  if targetOffset ≠ state.stack.length - 1 then
    if ¬ (state.isSwapReachable (← index state.stack.length targetOffset)) then
      throw (← state.blockSwapUnreachable (← index state.stack.length targetOffset))
    state ← state.swapWith targetOffset
  return ← buildBottomUp.loop (targetOffset + 1) state

theorem ru_requires_false {c : Prop} [Decidable c] (h : ¬ c) (r : String) :
    requires c r = .error (.assertion r) := by
  simp [requires, h]; rfl

theorem ru_blockSwap {source target : Stack} {spills : SpillSet} (state : State source target spills)
    (p : Fin state.stack.length) (hr : MAX_SWAP_DEPTH < state.stack.length - 1 - p) :
    state.blockSwapUnreachable p = .ok (.Blocked ⟨p, state.stack.length - 1 - p - MAX_SWAP_DEPTH⟩) := by
  unfold State.blockSwapUnreachable State.block
  rw [requires_of_true _ (by simp only [State.depthOf, Stack.offsetToDepth]; omega)]
  rfl

-- `placeTop` is the end of the loop body. The result never is `.finish`, so any
-- `state0` does.
theorem ru_placeTop (hswap : SwapWithStmt) {e : Bbu.Env} {src : Stack} (st : Bbu.St)
    (state state0 : OState e src) (t : Nat) (h : Rel e st state) :
    StepCorr e (Bbu.placeTop st t) state0 (ruTail t state) := by
  unfold Bbu.placeTop ruTail
  dsimp only
  by_cases hl : t < st.len
  · have hl' : t < state.stack.length := h.len ▸ hl
    rw [show index state.stack.length t = .ok ⟨t, hl'⟩ from index_eq ⟨t, hl'⟩, except_ok_bind]
    by_cases hf : st.dest t = t
    · rw [ite_eq_left (Or.inr hf)]
      have hf' : state.isFinal ⟨t, hl'⟩ := (h.isFinal ⟨t, hl'⟩).mpr hf
      exact ⟨_, by rw [ru_requires_false (not_not_intro hf')]; rfl, rfl⟩
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
      rw [except_ok_bind, ru_blockSwap _ _ (by simp only [MAX_SWAP_DEPTH, Bbu.MAX_SWAP_DEPTH] at hr ⊢; omega),
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

/-! ## The branch -/

theorem restUnbound_corr (hgen : GenerateStmt) (hswap : SwapWithStmt) : RestUnboundStmt := by
  intro e source st state t u uo h ht hu c4 c5 hpt
  rw [restUnbound_skip st state t u uo h hu c4 c5]
  have htt : t < (tgt e).length := by rw [tgt_length]; exact ht
  have hpt' : state.positionOf ⟨t, htt⟩ = none := by
    have := h.positionOf ⟨t, htt⟩
    rw [hpt, Option.map_eq_none_iff] at this
    exact this
  have hs : ¬((some t).isSome ∧ some t ≠ some t ∧ state.stack.length - t < MAX_SWAP_DEPTH) :=
    fun hc => hc.2.1 rfl
  have hidx : index (tgt e).length t = .ok ⟨t, htt⟩ := index_eq ⟨t, htt⟩
  unfold origRest
  rw [dite_eq_right_of_eq_false (eq_false hs)]
  simp only [Option.isNone_some, Bool.false_eq_true, false_and, ite_false, hidx, except_ok_bind, hpt']
  show StepCorr e _ state (state.generate t >>= fun s => index s.stack.length t >>= fun i =>
    if s.isFinal i then buildBottomUp.loop (t + 1) s else ruTail t s)
  have hg := hgen e source st state t h
  generalize Bbu.generate e st t = m at hg ⊢
  generalize state.generate t = r at hg ⊢
  cases m with
  | error err => cases r <;> simp only [Corr] at hg; exact ⟨_, rfl, hg⟩
  | ok st' =>
    cases r with
    | error _ => simp only [Corr] at hg
    | ok s =>
      simp only [Corr] at hg
      show StepCorr e (if t < st'.len ∧ st'.dest t = t then _ else _) state _
      by_cases hl : t < st'.len
      · have hl' : t < s.stack.length := hg.len ▸ hl
        rw [except_ok_bind, index_eq ⟨t, hl'⟩, except_ok_bind]
        by_cases hf : st'.dest t = t
        · rw [ite_eq_left ⟨hl, hf⟩, ite_eq_left ((hg.isFinal ⟨t, hl'⟩).mpr hf)]
          exact ⟨s, hg, rfl⟩
        · rw [ite_eq_right (fun h' => hf h'.2),
            ite_eq_right (fun h' => hf ((hg.isFinal ⟨t, hl'⟩).mp h'))]
          exact ru_placeTop hswap st' s state t hg
      · have hl' : ¬ t < s.stack.length := by rw [hg.len]; exact hl
        rw [ite_eq_right (fun h' => hl h'.1)]
        unfold Bbu.placeTop
        rw [ite_eq_left (Or.inl (by omega))]
        exact ⟨_, by rw [except_ok_bind]; simp [index, hl']; rfl, rfl⟩

end BbuBridge
