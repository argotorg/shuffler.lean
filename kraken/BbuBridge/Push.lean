import BbuBridge.Statements

/-!
`Bbu.add` with a push is `State.push`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- A mapping after a cast of its source length.
private theorem mpr_apply {m n k : Nat} (hc : Mapping m k = Mapping n k) (M : Mapping n k)
    (hmn : m = n) (i : Fin m) : (hc.mpr M) i = M (i.cast hmn) := by
  subst hmn; rfl

theorem push_corr : PushStmt := by
  intro e source st state v d hd h hc hv
  have hgen := hv
  have hpos := h.positionOf ⟨d, hd⟩
  rw [Bbu.add_eq]
  unfold State.push
  -- The destination is free: both add the slot. Else both fail.
  by_cases hp : state.mapping.positionOf ⟨d, hd⟩ = none
  · rw [hp] at hpos
    rw [← hpos]
    simp only [requires, hp, hgen, ↓reduceDIte, pure, Except.pure, bind, Except.bind,
      Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, h.pendingGenerations, ?_, ?_, ?_, h.target⟩
    · show state.stack ++ [decode v] = _
      simp [h.stack]
    · intro i
      simp only [mpr_apply _ _ (List.length_append ..) i]
      obtain ⟨i, hi⟩ := i
      have hl := h.len
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
      conv_rhs => rw [← encode_decode hc]
      revert hgen
      generalize decode v = x
      intro hgen
      cases x
      all_goals first
        | simp [traceOps, encodeOp, h.trace]
        | simp [Value.can_be_freely_generated, SpillSet.is_spilled] at hgen
    · exact h.pos.addState (by simpa [Bbu.Env.n] using hd) (by rw [← hpos]; rfl)
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact h.canon s hs
      · rw [List.mem_singleton.mp hs]; exact hc
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hp
    rw [hk] at hpos
    rw [← hpos]
    simp [requires, hp]
    trivial

end BbuBridge
