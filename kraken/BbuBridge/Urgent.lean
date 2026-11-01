module

public import BbuBridge.Statements
import all BbuBridge.Statements

@[expose] public section

/-!
`Bbu.urgent` (with `Bbu.urgentFrom`) is the `urgentToDup` scan of the loop.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

-- The body of the `urgentToDup` loop. The first component of the loop state is
-- the result of an early `return`.
private def scanBody {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (t offset : Nat)
    (acc : Option (Result source target spills) × Option Nat) :
    Except ShuffleErr (ForInStep (Option (Result source target spills) × Option Nat)) := do
  let urgentToDup := acc.2
  if (state.mapping.positionOf (← index target.length offset)).isSome then
    return ForInStep.yield (none, urgentToDup)
  let slot ← slotAt target offset
  if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
    return ForInStep.yield (none, urgentToDup)
  match state.stack.shallowestCopyPosition slot with
  | some sourceCopy =>
    if ¬ state.stack.isDupReachable sourceCopy then
      return ForInStep.done (some (← state.blockDupUnreachable sourceCopy), urgentToDup)
    if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ t ∧ urgentToDup.isNone then
      return ForInStep.yield (none, some offset)
    else return ForInStep.yield (none, urgentToDup)
  | _ => return ForInStep.yield (none, urgentToDup)

-- The end of the scan: the early result, or the rest.
private def scanEnd {α : Type} (rest : Option Nat → Except ShuffleErr α)
    (s : Option α × Option Nat) : Except ShuffleErr α :=
  match s.1 with
  | some r => pure r
  | none => rest s.2

-- `origScan` is the loop over the list of offsets from `t`.
private theorem origScan_eq {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (t : Nat)
    (rest : Option Nat → Except ShuffleErr (Result source target spills)) :
    origScan state t rest =
      forIn (List.range' t (target.length - t)) (none, none) (scanBody state t) >>= scanEnd rest := by
  unfold origScan
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', show [t:target.length].size = target.length - t by simp]
  rfl

variable {e : Bbu.Env} {source : Stack} {st : Bbu.St} {state : OState e source}

-- The test of the loop.
private theorem urgent_gen_iff (e : Bbu.Env) (source : Stack) (v : Bbu.StackSlot)
    (hv : decode v ∈ source ++ tgt e) :
    ((decode v).is_junk ∨ (decode v).can_be_freely_generated ∨ (spillSet e source).is_spilled (decode v)) ↔
      (Bbu.isJunk v || Bbu.canBeFreelyGenerated v || Bbu.isSpilled e v) = true := by
  rw [Bool.or_eq_true, Bool.or_eq_true, isJunk_iff, isFree_iff, isSpilled_iff e source v hv, or_assoc]

-- The scan from offset `d` on, with the related results `u` and `acc` so far.
private theorem urgent_scan (h : Rel e st state) (t : Nat)
    (restM : Nat → Bbu.M (Bbu.St × Bbu.Next))
    (restO : Option Nat → Except ShuffleErr (OResult e source))
    (hrest : ∀ u uo, UrgentRel e.n u uo → StepCorr e (restM u) state (restO uo)) :
    ∀ k d u acc, k = e.n - d → UrgentRel e.n u acc →
      StepCorr e ((Bbu.urgentFrom e st t d u).bind restM) state
        (forIn (List.range' d k) (none, acc) (scanBody state t) >>= scanEnd restO)
  | 0, d, u, acc, hk, hu => by
    rw [Bbu.urgentFrom]
    simp only [show ¬ d < e.n by omega, ↓reduceIte, List.range'_zero, List.forIn_nil]
    exact hrest u acc hu
  | k + 1, d, u, acc, hk, hu => by
    have hd : d < (tgt e).length := by rw [tgt_length]; omega
    have ih := urgent_scan h t restM restO hrest k (d + 1)
    rw [Bbu.urgentFrom, List.range'_succ, List.forIn_cons]
    unfold scanBody
    simp only [show d < e.n by omega, ↓reduceIte, index_eq ⟨d, hd⟩, except_ok_bind]
    have hp := h.positionOf ⟨d, hd⟩
    by_cases hs : (Bbu.positionOf st d).isSome
    · have hs' : (state.mapping.positionOf ⟨d, hd⟩).isSome := by
        rw [← Option.isSome_map (f := Fin.val), hp]; exact hs
      simp only [hs, hs', ↓reduceIte, pure, Except.pure, except_ok_bind]
      exact ih u acc (by omega) hu
    have hs' : ¬ (state.mapping.positionOf ⟨d, hd⟩).isSome := by
      rw [← Option.isSome_map (f := Fin.val), hp]; exact hs
    simp only [hs, hs', Bool.false_eq_true, ↓reduceIte, slotAt_index (tgt e) ⟨d, hd⟩, except_ok_bind,
      Fin.getElem_fin, tgt_get e d hd]
    have hmem : decode e.target[d]! ∈ source ++ tgt e := by
      rw [← tgt_get e d hd]; exact List.mem_append_right _ (List.getElem_mem hd)
    by_cases hg : (Bbu.isJunk e.target[d]! || Bbu.canBeFreelyGenerated e.target[d]! ||
        Bbu.isSpilled e e.target[d]!) = true
    · simp only [hg, (urgent_gen_iff e source _ hmem).mpr hg, ↓reduceIte, pure, Except.pure, except_ok_bind]
      exact ih u acc (by omega) hu
    simp only [hg, mt (urgent_gen_iff e source _ hmem).mp hg, Bool.false_eq_true, ↓reduceIte]
    have hc := h.shallowestCopyPosition (h.canonTarget d)
    cases hsc : state.stack.shallowestCopyPosition (decode e.target[d]!) with
    | none =>
      rw [hsc, Option.map_none] at hc
      rw [← hc]
      simp only [pure, Except.pure, except_ok_bind]
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
      · -- The copy is out of reach of a dup: both return the block.
        have hex : (state.depthOf c).val - MAX_DUP_DEPTH > 0 := by
          rw [hdepth]; exact Nat.sub_pos_of_lt hb
        simp only [hb, ↓reduceIte, hreach, not_true_eq_false, not_false_eq_true,
          State.blockDupUnreachable, State.block, requires_of_true _ hex, pure, Except.pure,
          except_ok_bind]
        refine ⟨state, h, ?_⟩
        simp only [scanEnd, hdepth, hm, pure, Except.pure]
      · have hn : acc.isNone = true ↔ u = e.n := by
          cases acc <;> simp [UrgentRel] at hu ⊢ <;> omega
        simp only [hb, ↓reduceIte, hreach, not_true_eq_false, not_false_eq_true, hdepth, hn, hm]
        by_cases hq : st.len - 1 - c.val = Bbu.MAX_DUP_DEPTH ∧ c.val ≠ t ∧ u = e.n
        · rw [ite_eq_left hq, ite_eq_left hq]
          simp only [pure, Except.pure, except_ok_bind]
          exact ih d (some d) (by omega) ⟨by omega, rfl⟩
        · rw [ite_eq_right hq, ite_eq_right hq]
          simp only [pure, Except.pure, except_ok_bind]
          exact ih u acc (by omega) hu

theorem urgent_corr : UrgentStmt := by
  intro e source st state t restM restO h hrest
  unfold Bbu.urgent
  rw [origScan_eq, tgt_length]
  exact urgent_scan h t restM restO hrest _ t e.n none rfl rfl

end BbuBridge
