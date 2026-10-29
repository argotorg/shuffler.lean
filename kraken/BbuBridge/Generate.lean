import BbuBridge.Statements

/-!
`Bbu.generate` is `State.generate`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- `Corr` goes through a bind.
theorem generate_corr_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Bbu.M α} {y : Except ShuffleErr β} {f : α → Bbu.M γ} {g : β → Except ShuffleErr δ}
    (h : Corr R x y) (hf : ∀ a b, R a b → Corr S (f a) (g b)) : Corr S (x.bind f) (y >>= g) := by
  cases x <;> cases y <;> simp_all [Corr, Except.bind, bind]

theorem generate_corr (hprod : ProduceStmt) (hswap : SwapWithStmt) (hdest : SwapDestStmt) :
    GenerateStmt := by
  intro e source st state d h
  unfold Bbu.generate State.generate
  dsimp only
  -- The offset is beyond the target.
  by_cases hn : e.n ≤ d
  · have : ¬ d < (tgt e).length := by rw [tgt_length]; omega
    rw [ite_eq_left hn]
    simp only [index, dite_eq_right this]
    rfl
  rw [ite_eq_right hn]
  have hd : d < (tgt e).length := by rw [tgt_length]; omega
  rw [show index (tgt e).length d = .ok ⟨d, hd⟩ from index_eq ⟨d, hd⟩, except_ok_bind]
  refine generate_corr_bind (hprod e source st state d hd h) fun st' state' h' => ?_
  have hl := h'.len
  -- The offset is the top or above.
  by_cases hlt : d + 1 < st'.len
  swap
  · rw [ite_eq_right (fun hh => hlt hh.1), ite_eq_right (show ¬ d + 1 < state'.stack.length by omega)]
    exact h'
  have hlt' : d + 1 < state'.stack.length := by omega
  have hdl : d < state'.stack.length := by omega
  rw [ite_eq_left hlt', show index state'.stack.length d = .ok ⟨d, hdl⟩ from index_eq ⟨d, hdl⟩,
    except_ok_bind]
  -- The offset holds its slot.
  by_cases hf : st'.dest d = d
  · rw [ite_eq_right (fun hh => hh.2 hf), ite_eq_right (not_not.mpr ((h'.isFinal ⟨d, hdl⟩).mpr hf))]
    exact h'
  rw [ite_eq_left ⟨hlt, hf⟩, ite_eq_left (mt (h'.isFinal ⟨d, hdl⟩).mp hf)]
  -- The slots at `d` and at the top.
  have hslot : ∀ i (hi : i < state'.stack.length), slotAt state'.stack i = .ok (decode (st'.val i)) := by
    intro i hi
    rw [← h'.get ⟨i, hi⟩]
    unfold slotAt
    rw [show index state'.stack.length i = .ok ⟨i, hi⟩ from index_eq ⟨i, hi⟩]
    rfl
  rw [hslot d hdl, hslot _ (by omega), except_ok_bind, except_ok_bind,
    show state'.stack.length - 1 = st'.len - 1 by omega]
  by_cases hv : st'.val d = st'.val (st'.len - 1)
  · -- An equal slot at `d` takes over the destination.
    rw [ite_eq_left hv, ite_eq_left ((decode_eq_iff (h'.canonVal _) (h'.canonVal _)).mpr hv)]
    obtain ⟨s, hs, hr⟩ := hdest e source st' state' d (st'.len - 1) h' (by omega) (by omega)
    rw [hs, except_ok_bind]
    exact hr
  rw [ite_eq_right hv, ite_eq_right (mt (decode_eq_iff (h'.canonVal _) (h'.canonVal _)).mp hv), except_ok_bind]
  -- A swap if the offset is in reach.
  have hreach : state'.isSwapReachable ⟨d, hdl⟩ ↔ st'.len - 1 - d ≤ Bbu.MAX_SWAP_DEPTH := by
    unfold State.isSwapReachable State.depthOf Stack.offsetToDepth
    rw [← hl]; rfl
  by_cases hr : st'.len - 1 - d ≤ Bbu.MAX_SWAP_DEPTH
  · rw [ite_eq_left hr, ite_eq_left (hreach.mpr hr), bind_pure]
    exact hswap e source st' state' d h'
  · rw [ite_eq_right hr, ite_eq_right (mt hreach.mp hr)]
    exact h'

end BbuBridge
