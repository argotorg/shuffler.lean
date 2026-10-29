import BbuBridge.Statements

/-!
`Bbu.urgent` (with `Bbu.urgentFrom`) is the `urgentToDup` scan of the loop.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The body of the `urgentToDup` loop.
private def urgentBody {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (t offset : Nat) (urgentToDup : Option Nat) :
    Except ShuffleErr (ForInStep (Option Nat)) := do
  if (state.positionOf (← index target.length offset)).isSome then
    return ForInStep.yield urgentToDup
  let slot ← slotAt target offset
  if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
    return ForInStep.yield urgentToDup
  if let some sourceCopy := state.stack.shallowestCopyPosition slot then
    if ¬ state.stack.isDupReachable sourceCopy then
      throw (← state.blockDupUnreachable sourceCopy)
    if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ t ∧ urgentToDup.isNone then
      return ForInStep.yield (some offset)
  return ForInStep.yield urgentToDup

-- `origUrgent` is the loop over the list of offsets from `t`.
private theorem origUrgent_eq {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (t : Nat) :
    origUrgent state t = forIn (List.range' t (target.length - t)) none (urgentBody state t) := by
  unfold origUrgent
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', bind_pure,
    show [t:target.length].size = target.length - t by simp]
  rfl

variable {e : Bbu.Env} {source : Stack} {st : Bbu.St} {state : OState e source}

-- The test of the loop.
private theorem urgent_gen_iff (e : Bbu.Env) (v : Bbu.StackSlot) :
    ((decode v).is_junk ∨ (decode v).can_be_freely_generated ∨ (spillSet e).is_spilled (decode v)) ↔
      (Bbu.isJunk v || Bbu.canBeFreelyGenerated v || Bbu.isSpilled e v) = true := by
  rw [Bool.or_eq_true, Bool.or_eq_true, isJunk_iff, isFree_iff, isSpilled_iff, or_assoc]

-- The scan from offset `d` on, with the related results `u` and `acc` so far.
private theorem urgent_scan (h : Rel e st state) (t : Nat) :
    ∀ k d u acc, k = e.n - d → UrgentRel e.n u acc →
      Corr (UrgentRel e.n) (Bbu.urgentFrom e st t d u)
        (forIn (List.range' d k) acc (urgentBody state t))
  | 0, d, u, acc, hk, hu => by
    rw [Bbu.urgentFrom]
    simp only [show ¬ d < e.n by omega, ↓reduceIte]
    exact hu
  | k + 1, d, u, acc, hk, hu => by
    have hd : d < (tgt e).length := by rw [tgt_length]; omega
    have ih := urgent_scan h t k (d + 1)
    rw [Bbu.urgentFrom, List.range'_succ, List.forIn_cons]
    unfold urgentBody
    simp only [show d < e.n by omega, ↓reduceIte, index_eq ⟨d, hd⟩, except_ok_bind]
    have hp := h.positionOf ⟨d, hd⟩
    by_cases hs : (Bbu.positionOf st d).isSome
    · have hs' : (state.positionOf ⟨d, hd⟩).isSome := by
        rw [← Option.isSome_map (f := Fin.val), hp]; exact hs
      simp only [hs, hs', ↓reduceIte]
      exact ih u acc (by omega) hu
    have hs' : ¬ (state.positionOf ⟨d, hd⟩).isSome := by
      rw [← Option.isSome_map (f := Fin.val), hp]; exact hs
    simp only [hs, hs', Bool.false_eq_true, ↓reduceIte, slotAt_index (tgt e) ⟨d, hd⟩, except_ok_bind,
      Fin.getElem_fin, tgt_get e d hd]
    by_cases hg : (Bbu.isJunk e.target[d]! || Bbu.canBeFreelyGenerated e.target[d]! ||
        Bbu.isSpilled e e.target[d]!) = true
    · simp only [hg, (urgent_gen_iff e _).mpr hg, ↓reduceIte]
      exact ih u acc (by omega) hu
    simp only [hg, mt (urgent_gen_iff e _).mp hg, Bool.false_eq_true, ↓reduceIte]
    have hc := h.shallowestCopyPosition (h.canonTarget d)
    cases hsc : state.stack.shallowestCopyPosition (decode e.target[d]!) with
    | none =>
      rw [hsc, Option.map_none] at hc
      rw [← hc]
      exact ih u acc (by omega) hu
    | some c =>
      rw [hsc, Option.map_some] at hc
      rw [← hc]
      have hdepth : (state.depthOf c).val = st.len - 1 - c.val := by
        simp [State.depthOf, Stack.offsetToDepth, h.len]
      have hreach : state.stack.isDupReachable c ↔ ¬ Bbu.MAX_DUP_DEPTH < st.len - 1 - c.val := by
        rw [Nat.not_lt, ← hdepth]; rfl
      have hm : MAX_DUP_DEPTH = Bbu.MAX_DUP_DEPTH := rfl
      by_cases hb : Bbu.MAX_DUP_DEPTH < st.len - 1 - c.val
      · -- The copy is out of reach of a dup.
        have hex : (state.depthOf c).val - MAX_DUP_DEPTH > 0 := by
          rw [hdepth]; exact Nat.sub_pos_of_lt hb
        simp only [hb, ↓reduceIte, hreach, not_true_eq_false, not_false_eq_true,
          State.blockDupUnreachable, State.block, requires_of_true _ hex]
        simp only [hdepth, hm]
        rfl
      · have hn : acc.isNone = true ↔ u = e.n := by
          cases acc <;> simp [UrgentRel] at hu ⊢ <;> omega
        simp only [hb, ↓reduceIte, hreach, not_true_eq_false, not_false_eq_true, hdepth, hn, hm]
        by_cases hq : st.len - 1 - c.val = Bbu.MAX_DUP_DEPTH ∧ c.val ≠ t ∧ u = e.n
        · rw [ite_eq_left hq, ite_eq_left hq]
          exact ih d (some d) (by omega) ⟨by omega, rfl⟩
        · rw [ite_eq_right hq, ite_eq_right hq]
          exact ih u acc (by omega) hu

theorem urgent_corr : UrgentStmt := by
  intro e source st state t h
  unfold Bbu.urgent
  rw [origUrgent_eq, tgt_length]
  exact urgent_scan h t _ t e.n none rfl rfl

end BbuBridge
