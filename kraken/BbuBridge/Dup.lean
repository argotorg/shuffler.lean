import BbuBridge.Statements

/-!
`Bbu.add` with a dup is `State.dup`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- A mapping after a cast of its source length.
private theorem mpr_apply {m n k : Nat} (hc : Mapping m k = Mapping n k) (M : Mapping n k)
    (hmn : m = n) (i : Fin m) : (hc.mpr M) i = M (i.cast hmn) := by
  subst hmn; rfl

-- A cast of the result stack does not change the operations of a trace.
private theorem traceOps_cast {spills : SpillSet} {source a b : Stack} (hab : a = b)
    (t : Trace spills source a) : traceOps (hab ▸ t) = traceOps t := by
  subst hab; rfl

theorem dup_corr : DupStmt := by
  intro e source st state c d hd h hc hdepth
  have hl := h.len
  have hcl : c < state.stack.length := hl ▸ hc
  have hpos := h.positionOf ⟨d, hd⟩
  rw [Bbu.add_eq]
  unfold State.dup
  rw [show index state.stack.length c = .ok ⟨c, hcl⟩ from index_eq ⟨c, hcl⟩, except_ok_bind]
  have hreach : state.stack.isDupReachable ⟨c, hcl⟩ := by
    simp only [Stack.isDupReachable, Stack.offsetToDepth, MAX_DUP_DEPTH]
    simp only [Bbu.MAX_DUP_DEPTH] at hdepth
    omega
  -- The destination is free: both add the slot. Else both fail.
  by_cases hp : state.positionOf ⟨d, hd⟩ = none
  · rw [hp] at hpos
    rw [← hpos]
    simp only [requires, hp, hreach, ↓reduceDIte, pure, Except.pure, bind, Except.bind,
      Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, h.pendingGenerations, ?_, ?_, ?_, h.target⟩
    · show state.stack ++ [state.stack[(⟨c, hcl⟩ : Fin _)]] = _
      rw [h.get ⟨c, hcl⟩]
      simp [h.stack]
    · intro i
      simp only [mpr_apply _ _ (List.length_append ..) i]
      obtain ⟨i, hi⟩ := i
      simp only [Bbu.St.len] at hl
      by_cases hlt : i < state.stack.length
      · rw [show Fin.cast _ ⟨i, hi⟩ = (⟨i, hlt⟩ : Fin _).castSucc from rfl,
          Mapping.push_apply_castSucc state.mapping ⟨d, hd⟩ hp, h.dest]
        simp [Bbu.St.dest, List.getElem?_append_left (show i < st.slots.length by omega)]
      · have hi' : i = state.stack.length := by simp at hi; omega
        subst hi'
        rw [show Fin.cast _ ⟨state.stack.length, hi⟩ = Fin.last _ from rfl,
          Mapping.push_apply_top state.mapping ⟨d, hd⟩ hp]
        simp [Bbu.St.dest, hl]
    · dsimp only
      rw [traceOps_cast]
      simp only [traceOps, encodeOp, List.map_append, h.trace, Stack.offsetToDepth, List.map_cons,
        List.map_nil]
      congr 3
      omega
    · exact h.pos.addState (by simpa [Bbu.Env.n] using hd) (by rw [← hpos]; rfl)
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact h.canon s hs
      · rw [List.mem_singleton.mp hs]; exact h.canonVal c
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hp
    rw [hk] at hpos
    rw [← hpos]
    simp [requires, hp]
    rfl

end BbuBridge
