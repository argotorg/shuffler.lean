import BbuBridge.Statements

/-!
`Bbu.produce` (with `Bbu.emit`) is `State.produce`.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- `Corr` goes through a bind.
theorem produce_corr_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : Bbu.M α} {y : Except ShuffleErr β} {f : α → Bbu.M γ} {g : β → Except ShuffleErr δ}
    (h : Corr R x y) (hf : ∀ a b, R a b → Corr S (f a) (g b)) : Corr S (x.bind f) (y >>= g) := by
  cases x <;> cases y <;> simp_all [Corr, Except.bind, bind]

theorem produce_corr (hpush : PushStmt) (hdup : DupStmt) : ProduceStmt := by
  intro e source st state d hd h
  -- The check after the push or dup.
  have hfin : ∀ (st' : Bbu.St) (state' : OState e source), Rel e st' state' →
      Corr (Rel e)
        (if Bbu.positionOf st' d ≠ some (st'.len - 1) then .error .assertion
          else .ok { st' with pending := st'.pending - 1 })
        (do
          let _ ← requires ((state'.positionOf ⟨d, hd⟩).map Fin.val = some (state'.stack.length - 1))
            "generated slot is not bound to the top"
          pure { state' with pending_generations := state'.pending_generations - 1 }) := by
    intro st' state' h'
    rw [← h'.positionOf ⟨d, hd⟩, ← h'.len]
    by_cases hc : (state'.positionOf ⟨d, hd⟩).map Fin.val = some (state'.stack.length - 1)
    · rw [requires_of_true _ hc, ite_eq_right (not_not.mpr hc)]
      exact ⟨h'.stack, h'.dest, by simp [h'.pending], h'.ops⟩
    · rw [ite_eq_left hc]
      simp only [requires, dite_eq_right hc]
      rfl
  -- A push of a free or spilled value.
  have hpush' : ∀ v : Bbu.Word,
      (decode v).can_be_freely_generated ∨ (spillSet e).is_spilled (decode v) →
      Corr (Rel e) ((Bbu.add st v d (.push v)).bind _) (state.push (decode v) ⟨d, hd⟩ >>= _) :=
    fun v hg => produce_corr_bind (hpush e source st state v d hd h
      (by rwa [isFree_iff, isSpilled_iff])) hfin
  unfold Bbu.produce Bbu.emit State.produce
  dsimp only
  rw [tgt_get e d hd]
  generalize e.target[d]! = v
  -- A wildcard.
  by_cases h0 : v = 0
  · rw [ite_eq_left h0, ite_eq_left ((isJunk_iff v).mpr h0)]
    exact hpush' v (.inl ((isFree_iff v).mp (by simp [h0, Bbu.isFree])))
  rw [ite_eq_right h0, ite_eq_right (mt (isJunk_iff v).mp h0)]
  have hfree : (decode v).can_be_freely_generated ∨ (spillSet e).is_spilled (decode v) ↔
      (Bbu.isFree v || Bbu.isSpilled e v) = true := by
    rw [Bool.or_eq_true, isFree_iff, isSpilled_iff]
  have hc := h.shallowestCopy v
  cases hco : state.stack.shallowestCopyPosition (decode v) with
  | none =>
    -- No copy: a push, or an assertion.
    rw [hco, Option.map_none] at hc
    rw [← hc]
    simp only [Option.filter_none]
    by_cases hg : (decode v).can_be_freely_generated ∨ (spillSet e).is_spilled (decode v)
    · rw [ite_eq_left hg, ite_eq_left (hfree.mp hg)]
      exact hpush' v hg
    · rw [ite_eq_right hg, ite_eq_right (mt hfree.mpr hg)]
      rfl
  | some pos =>
    rw [hco, Option.map_some] at hc
    rw [← hc]
    -- The copy holds `v`.
    have hpv : st.val pos = v := by
      have := List.find?_some hco
      simp only [decide_eq_true_eq] at this
      rw [h.get] at this
      exact decode_injective this
    have hpl : pos.val < st.len := h.len ▸ pos.isLt
    have hreach : state.stack.isDupReachable pos ↔ st.len - 1 - pos.val ≤ Bbu.MAX_DUP_DEPTH := by
      unfold Stack.isDupReachable Stack.offsetToDepth
      rw [← h.len]; rfl
    by_cases hr : st.len - 1 - pos.val ≤ Bbu.MAX_DUP_DEPTH
    · -- A dup of the copy.
      simp only [Option.filter_some, decide_eq_true (hreach.mpr hr), decide_eq_true hr, ite_true]
      have := hdup e source st state pos.val d hd h hpl hr
      rw [hpv] at this
      exact produce_corr_bind this hfin
    simp only [Option.filter_some, decide_eq_false (mt hreach.mp hr), decide_eq_false hr,
      Bool.false_eq_true, ite_false]
    by_cases hg : (decode v).can_be_freely_generated ∨ (spillSet e).is_spilled (decode v)
    · rw [ite_eq_left hg, ite_eq_left (hfree.mp hg)]
      exact hpush' v hg
    -- The copy is out of dup reach.
    rw [ite_eq_right hg, ite_eq_right (mt hfree.mpr hg)]
    have hx : (state.depthOf pos).val - MAX_DUP_DEPTH > 0 := by
      have := h.len
      unfold State.depthOf Stack.offsetToDepth
      simp only [Bbu.MAX_DUP_DEPTH] at hr
      simp only [MAX_DUP_DEPTH]; omega
    simp only [Option.isSome_some, ↓reduceDIte, Option.get_some, State.blockDupUnreachable,
      State.block, requires_of_true _ hx]
    show Bbu.Err.blocked _ _ = encodeErr (.Blocked _)
    simp [encodeErr, State.depthOf, Stack.offsetToDepth, h.len, Bbu.MAX_DUP_DEPTH, MAX_DUP_DEPTH]

end BbuBridge
