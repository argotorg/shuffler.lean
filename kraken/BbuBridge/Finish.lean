import BbuBridge.Statements

/-!
`Bbu.finish` is the final permutation of the loop and the check after the loop.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The stack after a swap with the slot at `depth` below the top.
def swapStack (s : Stack) (depth : Nat) : Stack := s.swap (s.length - 1) (s.length - 1 - depth)

-- A trace of swaps only: the stack after the swaps.
theorem trace_swaps {spills : SpillSet} {a b : Stack} (t : Trace spills a b) :
    ∀ swaps : List Nat, traceOps t = swaps.map TraceOp.swap → b = swaps.foldl swapStack a := by
  induction t with
  | Lit =>
    intro swaps h
    cases swaps with
    | nil => rfl
    | cons _ _ => simp [traceOps] at h
  | Swap idx _ _ _ t ih =>
    intro swaps h
    obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h.symm
    obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp h2
    cases hx
    rw [List.foldl_append, ← ih l₁ h1.symm]
    rfl
  | Dup _ _ _ _ _ _ | Pop _ _ _ | Push _ _ _ _ | Load _ _ _ _ =>
    intro swaps h
    obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h.symm
    obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp h2
    cases hx

theorem swapTop_map (st : Bbu.St) (d : Nat) :
    (Bbu.swapTop st d).slots.map (fun s => decode s.val)
      = swapStack (st.slots.map fun s => decode s.val) d := by
  rcases Nat.eq_zero_or_pos st.slots.length with h0 | hpos
  · simp [Bbu.swapTop, swapStack, List.eq_nil_of_length_eq_zero h0]
  · rw [swapStack, List.swap_eq_of_lt (by simp; omega) (by simp; omega)]
    apply List.ext_getElem
    · simp [Bbu.swapTop]
    · intro i h1 h2
      have ht : st.slots.length - 1 < st.slots.length := by omega
      have hj : st.slots.length - 1 - d < st.slots.length := by omega
      simp only [Bbu.swapTop, Bbu.St.len, Bbu.St.val, List.getElem_map, List.getElem_set,
        List.length_map]
      split_ifs <;> simp_all

theorem foldl_swapTop_map (swaps : List Nat) (st : Bbu.St) :
    (swaps.foldl Bbu.swapTop st).slots.map (fun s => decode s.val)
      = swaps.foldl swapStack (st.slots.map fun s => decode s.val) := by
  induction swaps generalizing st with
  | nil => rfl
  | cons d ds ih => simp only [List.foldl_cons, ih, swapTop_map]

theorem foldl_swapTop_canon (swaps : List Nat) (st : Bbu.St) (hc : ∀ s ∈ st.slots, Canon s.val) :
    ∀ s ∈ (swaps.foldl Bbu.swapTop st).slots, Canon s.val := by
  induction swaps generalizing st with
  | nil => exact hc
  | cons d ds ih =>
    exact ih _ (canon_set (canon_set hc (canon_val hc _)) (canon_val hc _))

theorem finish_corr : FinishStmt := by
  intro e source st state h
  have hl := h.len
  by_cases hn : st.len = e.n
  swap
  · -- The sizes differ: both fail with an assertion.
    have hne : ¬ state.stack.length = e.target.length := by rw [hl]; exact hn
    simp only [hn, ite_false, origFinish, requires, tgt, List.length_map, hne, dite_false]
    rfl
  rw [ite_eq_left hn]
  have hlen : state.stack.length = (tgt e).length := by rw [hl, tgt_length, hn]
  have hbound : ∀ i, (state.destinationOf i).isSome := fun i => by
    obtain ⟨j, hj, -⟩ := h.mapping i
    simp [State.destinationOf, hj]
  -- The model destinations are the original permutation.
  have hds : st.slots.map Bbu.Slot.dest = destList (state.mapping.toPermutation hlen hbound) := by
    apply List.ext_getElem
    · simp [length_destList, hl, Bbu.St.len]
    intro k hk _
    have hk' : k < state.stack.length := by simp [hl, Bbu.St.len] at hk ⊢; omega
    have ha := Mapping.toPermutation_apply state.mapping hlen hbound ⟨k, hk'⟩
    have hd := h.dest ⟨k, hk'⟩
    rw [← ha] at hd
    simp only [Option.map_some, Option.some_inj, Fin.val_cast] at hd
    simp [destList, hd, h.slot_dest k (by simpa using hk)]
  have hperm : Bbu.IsPerm (st.slots.map Bbu.Slot.dest) := by
    have hd := h.dests
    have hdl := st.length_dests
    simp only [Bbu.St.dests] at hd hdl
    exact ⟨fun i hi => by have := hd.1 i hi; omega, hd.2⟩
  -- After the two checks, `origFinish` is the original permutation.
  have hof : origFinish state =
      (Shuffler.Permute.permute (spillSet e) state.stack
        (state.mapping.toPermutation hlen hbound)).bind
        fun r => .ok ⟨r.1, state.trace.concat r.2⟩ := by
    simp only [origFinish, requires, dite_eq_left hlen, dite_eq_left hbound]
    rfl
  rw [hof]
  unfold Bbu.finish
  simp only [Bbu.St.all_destinationOf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [dite_eq_left hperm]
  split
  · -- The swaps of the model: the original gives the same swaps after the loop ops.
    rename_i swaps hp
    obtain ⟨res, trace, ho, hops, hres⟩ :=
      permute_ok_of_model (spillSet e) state.stack _ _ hds hp
    have hrl : res.length = (tgt e).length := by
      rw [hres, Shuffler.Permute.apply_permutation, List.length_ofFn, hlen]
    have hpost : post (tgt e) (.ok ⟨res, state.trace.concat trace⟩) =
        .ok ⟨res, state.trace.concat trace⟩ := by
      unfold post
      rw [except_ok_bind]
      dsimp only
      rw [requires_of_true _ hrl]
      rfl
    rw [ho]
    show Corr ResRel _ (post (tgt e) (.ok ⟨res, state.trace.concat trace⟩))
    rw [hpost]
    obtain ⟨-, -, -, htr⟩ := Bbu.foldl_swapTop swaps st
    refine ⟨?_, ?_, foldl_swapTop_canon swaps st h.canon⟩
    · show res = _
      rw [foldl_swapTop_map, ← h.stack]
      exact trace_swaps trace swaps hops
    · show (traceOps (state.trace.concat trace)).map encodeOp = _
      rw [htr]
      simp [traceOps_concat, ← h.trace, hops, encodeOp]
  · -- Blocked: the original is blocked at the same offset.
    rename_i b hp
    rw [permute_blocked_of_model _ _ _ _ hds hp]
    rfl

end BbuBridge
