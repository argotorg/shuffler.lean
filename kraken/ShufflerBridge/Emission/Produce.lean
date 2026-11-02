module

public import ShufflerBridge.Emission.Statements
import all ShufflerBridge.Emission.Statements

@[expose] public section

/-!
`FlatShuffler.produce` (with `FlatShuffler.emit`) is `State.produce`.
-/

namespace ShufflerBridge.Emission

open Shuffler Shuffler.Emission

-- `Corr` and then `ResCorr` go through a bind.
theorem produce_corr_bind {α β : Type} {source target : Stack} {spills : SpillSet}
    {R : α → β → Prop} {S : FlatShuffler.St → State source target spills → Prop}
    {x : FlatShuffler.M α} {y : Except ShuffleErr β} {f : α → FlatShuffler.M FlatShuffler.St}
    {g : β → Except ShuffleErr (Result source target spills)}
    (h : Corr R x y) (hf : ∀ a b, R a b → ResCorr S (f a) (g b)) :
    ResCorr S (x.bind f) (y >>= g) := by
  rcases x with (_ | _) | a <;> rcases y with (_ | _) | b <;>
    simp_all [Corr, ResCorr, Except.bind, bind]

-- `add` keeps `pendingGenerations`.
theorem produce_corr_add {β : Type} {R : FlatShuffler.St → β → Prop} {st : FlatShuffler.St} {v : FlatShuffler.StackSlot}
    {d : Nat} {op : FlatShuffler.Op} {y : Except ShuffleErr β} (h : Corr R (FlatShuffler.add st v d op) y)
    (hp : 0 < st.pendingGenerations) :
    Corr (fun a b => R a b ∧ 0 < a.pendingGenerations) (FlatShuffler.add st v d op) y :=
  corr_mono h fun _ _ hx hr => ⟨hr, by rw [FlatShuffler.add_pending hx]; exact hp⟩

-- The FRL check of `emit` keeps `pendingGenerations`.
theorem produce_corr_dup {β : Type} {R : FlatShuffler.St → β → Prop} {st : FlatShuffler.St} {v : FlatShuffler.StackSlot}
    {d : Nat} {op : FlatShuffler.Op} {y : Except ShuffleErr β}
    (h : Corr R (if v.kind == FlatShuffler.FunctionReturnLabel then .error .assertion else FlatShuffler.add st v d op) y)
    (hp : 0 < st.pendingGenerations) :
    Corr (fun a b => R a b ∧ 0 < a.pendingGenerations)
      (if v.kind == FlatShuffler.FunctionReturnLabel then .error .assertion else FlatShuffler.add st v d op) y :=
  corr_mono h fun _ _ hx hr => ⟨hr, by
    split at hx
    · cases hx
    · rw [FlatShuffler.add_pending hx]; exact hp⟩

theorem produce_corr (hpush : PushStmt) (hdup : DupStmt) : ProduceStmt := by
  intro e source st state d hd h hp0
  -- The check after the push or dup.
  have hfin : ∀ (st' : FlatShuffler.St) (state' : OState e source),
      Rel e st' state' ∧ 0 < st'.pendingGenerations →
      ResCorr (Rel e)
        (if FlatShuffler.positionOf st' d ≠ some (st'.len - 1) then .error .assertion
          else .ok { st' with pendingGenerations := FlatShuffler.sizeDec st'.pendingGenerations })
        (do
          let _ ← requires ((state'.mapping.positionOf ⟨d, hd⟩).map Fin.val =
            some (state'.stack.length - 1)) "generated slot is not bound to the top"
          pure ⟨none, { state' with pending_generations := state'.pending_generations - 1 }⟩) := by
    intro st' state' ⟨h', hp'⟩
    rw [← h'.positionOf ⟨d, hd⟩, ← h'.len]
    by_cases hc : (state'.mapping.positionOf ⟨d, hd⟩).map Fin.val = some (state'.stack.length - 1)
    · rw [requires_of_true _ hc, ite_eq_right (not_not.mpr hc)]
      exact ⟨rfl, h'.stack, h'.dest, by simp [h'.pendingGenerations, FlatShuffler.sizeDec_pos hp'], h'.trace,
        h'.pos.congr rfl rfl, h'.canon, h'.target⟩
    · rw [ite_eq_left hc]
      simp only [requires, dite_eq_right hc]
      trivial
  -- A push of a free or spilled value.
  have hpush' : ∀ v : FlatShuffler.StackSlot, StackSlotHasCanonicalEncoding v →
      (decodeStackSlot v).can_be_freely_generated ∨ (spilledVariables e source).is_spilled (decodeStackSlot v) →
      ResCorr (Rel e) ((FlatShuffler.add st v d (.push v)).bind _) (state.push (decodeStackSlot v) ⟨d, hd⟩ >>= _) :=
    fun v hv hg => produce_corr_bind (produce_corr_add (hpush e source st state v d hd h hv
      hg) hp0) hfin
  unfold FlatShuffler.produce FlatShuffler.emit State.produce
  dsimp only
  rw [tgt_get e d hd]
  have hcv := h.canonTarget d
  have hmem : decodeStackSlot e.target[d]! ∈ source ++ decodedTargetStack e := by
    rw [← tgt_get e d hd]; exact List.mem_append_right _ (List.getElem_mem hd)
  revert hcv hmem
  generalize e.target[d]! = v
  intro hcv hmem
  -- A wildcard.
  by_cases h0 : FlatShuffler.isJunk v = true
  · rw [ite_eq_left h0, ite_eq_left ((isJunk_iff v).mpr h0)]
    exact hpush' v hcv (.inl ((isFree_iff v).mp (by unfold FlatShuffler.isJunk at h0; simp [FlatShuffler.canBeFreelyGenerated, h0])))
  rw [ite_eq_right h0, ite_eq_right (mt (isJunk_iff v).mp h0)]
  have hfree : (decodeStackSlot v).can_be_freely_generated ∨ (spilledVariables e source).is_spilled (decodeStackSlot v) ↔
      (FlatShuffler.canBeFreelyGenerated v || FlatShuffler.isSpilled e v) = true := by
    rw [Bool.or_eq_true, isFree_iff, isSpilled_iff e source v hmem]
  have hc := h.shallowestCopyPosition hcv
  cases hco : state.stack.shallowestCopyPosition (decodeStackSlot v) with
  | none =>
    -- No copy: a push, or an assertion.
    rw [hco, Option.map_none] at hc
    rw [← hc]
    simp only [Option.filter_none]
    by_cases hg : (decodeStackSlot v).can_be_freely_generated ∨ (spilledVariables e source).is_spilled (decodeStackSlot v)
    · rw [ite_eq_left hg, ite_eq_left (hfree.mp hg)]
      exact hpush' v hcv hg
    · rw [ite_eq_right hg, ite_eq_right (mt hfree.mpr hg)]
      trivial
  | some pos =>
    rw [hco, Option.map_some] at hc
    rw [← hc]
    -- The copy holds `v`.
    have hpv : st.val pos = v := by
      have := List.find?_some hco
      simp only [decide_eq_true_eq] at this
      rw [h.get] at this
      exact decode_inj (h.canonVal _) hcv this
    have hpl : pos.val < st.len := h.len ▸ pos.isLt
    have hreach : state.stack.isDupReachable pos ↔ st.len - 1 - pos.val ≤ FlatShuffler.MAX_DUP_DEPTH := by
      unfold Stack.isDupReachable Stack.offsetToDepth
      rw [← h.len]; rfl
    by_cases hr : st.len - 1 - pos.val ≤ FlatShuffler.MAX_DUP_DEPTH
    · -- A dup of the copy.
      simp only [Option.filter_some, decide_eq_true (hreach.mpr hr), decide_eq_true hr, ite_true]
      have := hdup e source st state pos.val d hd h hpl hr
      rw [hpv] at this
      exact produce_corr_bind (produce_corr_dup this hp0) hfin
    simp only [Option.filter_some, decide_eq_false (mt hreach.mp hr), decide_eq_false hr,
      Bool.false_eq_true, ite_false]
    by_cases hg : (decodeStackSlot v).can_be_freely_generated ∨ (spilledVariables e source).is_spilled (decodeStackSlot v)
    · rw [ite_eq_left hg, ite_eq_left (hfree.mp hg)]
      exact hpush' v hcv hg
    -- The copy is out of dup reach.
    rw [ite_eq_right hg, ite_eq_right (mt hfree.mpr hg)]
    have hx : (state.depthOf pos).val - MAX_DUP_DEPTH > 0 := by
      have := h.len
      unfold State.depthOf Stack.offsetToDepth
      simp only [FlatShuffler.MAX_DUP_DEPTH] at hr
      simp only [MAX_DUP_DEPTH]; omega
    simp only [Option.isSome_some, ↓reduceDIte, Option.get_some, State.blockDupUnreachable,
      State.block, requires_of_true _ hx]
    refine ⟨?_, h⟩
    simp [State.depthOf, Stack.offsetToDepth, h.len, FlatShuffler.MAX_DUP_DEPTH, MAX_DUP_DEPTH]

end ShufflerBridge.Emission
