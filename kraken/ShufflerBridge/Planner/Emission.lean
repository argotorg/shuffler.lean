module

public import ShufflerBridge.Planner.List
import all ShufflerBridge.Planner.List
public import ShufflerBridge.Planner.Loops
import all ShufflerBridge.Planner.Loops
public import ShufflerBridge.Planner.Frame
import all ShufflerBridge.Planner.Frame
public import Shuffler.Emission.Run.Lemmas.Execution
import all Shuffler.Emission.Run.Lemmas.Execution

@[expose] public section

/-!
The flat `emissionRun` and PR31 `Emission.run` (`emissionRun_erel`). The checks of `run` after
`permuteAtLowestHeight` give the same result on the two sides (`avail_iff`, `labels_iff`), and
`buildBottomUp` too (`bbu_erel`).
-/

namespace ShufflerBridge.Planner

open Shuffler Shuffler.Emission ShufflerBridge.Emission
open FlatShuffler.Flat (get optOf optW absMapping NONE)

theorem requires_of_false (c : Prop) [Decidable c] (h : ¬c) (r : String) :
    requires c r = .error (.assertion r) := by
  simp only [requires, dite_eq_right h]; rfl

section
variable {e : FlatShuffler.Env} {source : Stack} {fs : FlatShuffler.Flat.St} {st : FlatShuffler.St}
  {state : OState e source}

/-! ## The checks -/

theorem avail_one (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state) (i : Fin (decodedTargetStack e).length) :
    FlatShuffler.Flat.isAvailable fs (BitVec.ofNat 64 i.val) = true ↔ state.isAvailable i := by
  have hn := hs.n
  have hle := hs.n_le
  have htl := tgt_length e
  have hw : (BitVec.ofNat 64 i.val).toNat = i.val := FlatShuffler.Flat.toNat_ofNat_lt (by omega)
  have ht := hs.target (t := BitVec.ofNat 64 i.val) (by rw [hw]; omega)
  rw [hw] at ht
  have hv : (decodedTargetStack e)[i.val] = decodeStackSlot e.target[i.val]! := tgt_get e i.val i.isLt
  have hc := h.canonTarget i.val
  have hcopy := h.shallowestCopyPosition hc
  have hlen := h.len
  have hx : ∀ p, FlatShuffler.shallowestCopyPosition st e.target[i.val]! = some p → p < 2 ^ 64 - 1 := by
    intro p hp
    rw [← hcopy] at hp
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hp
    have := q.isLt
    have := hs.len_lt
    unfold FlatShuffler.maxStackSize at this
    omega
  unfold FlatShuffler.Flat.isAvailable State.isAvailable
  dsimp only
  rw [← ht, FlatShuffler.Flat.sim_copy hs, ← hs.isSpilled, Fin.getElem_fin, hv]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [FlatShuffler.Flat.optW_ne_NONE hx, isFree_iff,
    isSpilled_iff e source _ (List.mem_append_right _ (hv ▸ List.getElem_mem i.isLt)), ← hcopy,
    Option.isSome_map, or_assoc]

theorem avail_iff (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state) :
    FlatShuffler.Flat.availableFrom fs 0 = true ↔ ∀ i, state.isAvailable i := by
  have hn := hs.n
  have htl := tgt_length e
  rw [FlatShuffler.Flat.availableFrom_iff fs hs.n_le]
  constructor
  · intro hall i
    exact (avail_one hs h i).mp (hall i.val (by omega))
  · intro hall d hd
    exact (avail_one hs h ⟨d, by omega⟩).mpr (hall _)

theorem labels_one (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state) (j : Fin (decodedTargetStack e).length) :
    ((get fs.target (BitVec.ofNat 64 j.val)).kind ≠ FlatShuffler.FunctionReturnLabel
        || get fs.pos (BitVec.ofNat 64 j.val) ≠ NONE) = true ↔
      ((decodedTargetStack e)[j.val].isFunctionReturnLabel → (state.mapping.symm j).isSome) := by
  have hn := hs.n
  have hle := hs.n_le
  have htl := tgt_length e
  have hw : (BitVec.ofNat 64 j.val).toNat = j.val := FlatShuffler.Flat.toNat_ofNat_lt (by omega)
  have ht := hs.target (t := BitVec.ofNat 64 j.val) (by rw [hw]; omega)
  rw [hw] at ht
  have hp := hs.pos_ne_NONE (d := BitVec.ofNat 64 j.val) (by rw [hw]; omega)
  rw [hw, ← h.positionOf j, Option.isSome_map] at hp
  rw [← ht, tgt_get e j.val j.isLt, isFRL_iff (h.canonTarget j.val)]
  simp only [Mapping.positionOf] at hp
  by_cases hk : e.target[j.val]!.kind = FlatShuffler.FunctionReturnLabel
  · simp only [hk, ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq,
      forall_const, hp]
  · simp only [hk, ne_eq, not_false_eq_true, decide_true, Bool.true_or, false_implies]

theorem labels_iff (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state) :
    FlatShuffler.Flat.labelsFrom fs 0 = true ↔ ∀ j : Fin (decodedTargetStack e).length,
      ((decodedTargetStack e)[j.val]'j.isLt).isFunctionReturnLabel → (state.mapping.symm j).isSome := by
  have hn := hs.n
  have htl := tgt_length e
  rw [FlatShuffler.Flat.labelsFrom_iff fs hs.n_le]
  constructor
  · intro hall j
    exact (labels_one hs h j).mp (hall j.val (by omega))
  · intro hall d hd
    exact (labels_one hs h ⟨d, by omega⟩).mpr (hall _)

-- The size check passes on both sides.
theorem size_ok (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state)
    (hsize : state.stack.length + state.pending_generations = (decodedTargetStack e).length) :
    fs.size + fs.pend = fs.targetSize := by
  have hn := hs.n
  have hle := hs.n_le
  have htl := tgt_length e
  have h1 := hs.size
  have h2 := hs.pend
  have h3 := h.len
  have h4 := h.pendingGenerations
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  unfold FlatShuffler.maxStackSize at hle
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

-- The count check passes on both sides.
theorem unmapped_ok (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state)
    (hpending : state.mapping.unmapped_target_slots = state.pending_generations) :
    FlatShuffler.Flat.unmappedFrom fs 0 0 = fs.pend := by
  have hle := hs.n_le
  have hmap := (out_of hs h).map
  simp only [absMapping, absP, FlatShuffler.Map.Mapping.mk.injEq] at hmap
  rw [FlatShuffler.Flat.unmappedFrom_eq fs hle, FlatShuffler.Flat.countP_none' _ _ hle, hmap.2]
  have hc := absP_count state.mapping
  simp only [absP] at hc
  rw [hc, hpending, h.pendingGenerations, ← hs.pend, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## `buildBottomUp` -/

theorem bbu_erel (hs : FlatShuffler.Flat.Sim e fs st) (h : Rel e st state) (hv : state.Valid) :
    ERel (FlatShuffler.Flat.buildBottomUp fs) (buildBottomUp state hv) := by
  have hn := hs.n
  have htl := tgt_length e
  have hi : FlatShuffler.InvS e st 0 := by
    refine ⟨?_, hs.n ▸ hs.n_le, Nat.zero_le _, h.pos⟩
    have := hv.1
    rw [h.len, h.pendingGenerations, htl] at this
    exact this
  have hl := FlatShuffler.Flat.sim_loop (FlatShuffler.Flat.permR e) fs st 0 hs hi (Nat.zero_le _)
  rw [buildBottomUp_eq_post]
  exact erel_of hl (loop_corr' e source st state 0 h)

end
/-! ## `Emission::run` -/

-- The members of the constructor state that the loop on `m_pendingGenerations` does not write.
theorem ctorP_fields (data : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) (m : FlatShuffler.Word)
    (target : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) (n : FlatShuffler.Word) (M : FlatShuffler.Flat.Mapping)
    (spills : BitVec 32 → BitVec 8) (u : FlatShuffler.Flat.Uninit) :
    let fs := FlatShuffler.Flat.ctorP data m target n M spills u
    fs.size = m ∧ fs.target = target ∧ fs.targetSize = n ∧ fs.spills = spills ∧ fs.data = data := by
  unfold FlatShuffler.Flat.ctorP
  dsimp only
  rw [FlatShuffler.Flat.pend_fold]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem out_pop {e : FlatShuffler.Env} {source : Stack} {fs : FlatShuffler.Flat.St} {state : OState e source}
    {A : FlatShuffler.Map.Mapping} (h : PopRel (FlatShuffler.Flat.absSt A fs) state) (hs : fs.size.toNat ≤ FlatShuffler.maxStackSize)
    (ht : fs.targetSize.toNat ≤ FlatShuffler.maxStackSize) : Out fs state :=
  ⟨h.mapping, h.stack.symm, h.trace, hs, ht⟩

theorem emissionRun_erel (data target : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) (m n : FlatShuffler.Word)
    (hm : m.toNat ≤ FlatShuffler.maxStackSize) (hn : n.toNat ≤ FlatShuffler.maxStackSize) (M : FlatShuffler.Flat.Mapping)
    (spills : BitVec 32 → BitVec 8) (u : FlatShuffler.Flat.Uninit) (l : FlatShuffler.Flat.Locals) {e : FlatShuffler.Env}
    (he : e = FlatShuffler.Flat.listEnv n.toNat target spills)
    (P : Mapping ((data.toList.take m.toNat).map decodeStackSlot).length (decodedTargetStack e).length)
    (hP : absMapping M.dest M.pos m n = absP P)
    (hcs : ∀ v ∈ data.toList.take m.toNat, StackSlotHasCanonicalEncoding v) (hct : ∀ v ∈ e.target, StackSlotHasCanonicalEncoding v) :
    ERel (FlatShuffler.Flat.emissionRun M.pos l (FlatShuffler.Flat.ctorP data m target n M spills u))
      (Emission.run ((data.toList.take m.toNat).map decodeStackSlot) (decodedTargetStack e) P
        (spilledVariables e ((data.toList.take m.toNat).map decodeStackSlot))) := by
  obtain ⟨hf0s, hf0t, hf0n, hf0p, hf0d⟩ := ctorP_fields data m target n M spills u
  generalize hfs0 : FlatShuffler.Flat.ctorP data m target n M spills u = fs0 at hf0s hf0t hf0n hf0p hf0d
  have hA := FlatShuffler.Flat.ctorP_abs data m target n M spills u hm hn
  rw [hfs0, hP] at hA
  have hrs := FlatShuffler.Flat.removeSurplus_abs (absP P) fs0 (by rw [hf0s]; exact hm)
  rw [hA] at hrs
  let initial : OState e ((data.toList.take m.toNat).map decodeStackSlot) := {
    planned_mapping := P, stack := (data.toList.take m.toNat).map decodeStackSlot,
    trace := .Lit _, mapping := P, pending_generations := P.unmapped_target_slots }
  have hc := removeSurplus_corr_canon (init_rel (target := decodedTargetStack e)
    (spills := spilledVariables e ((data.toList.take m.toNat).map decodeStackSlot)) _ P) hcs
  rw [hrs] at hc
  change Corr _ _ (removeSurplus initial) at hc
  obtain ⟨removed, hr⟩ := removeSurplus_ok initial
  obtain ⟨hrplan, hrpending, -⟩ := removeSurplus_frame initial hr
  have hfr := FlatShuffler.Flat.removeSurplus_frame fs0
  unfold Emission.run FlatShuffler.Flat.emissionRun
  change ERel _ (removeSurplus initial >>= _)
  rw [hr, except_ok_bind]
  rw [hr] at hc
  generalize FlatShuffler.Flat.removeSurplus fs0 = r1 at hc hfr ⊢
  obtain ⟨s1, fs1⟩ := r1
  dsimp only at hfr ⊢
  cases s1 with
  | assertionFailed => exact hc.elim
  | blocked =>
    simp only [FlatShuffler.Flat.absOut, Corr, SurplusRel, Option.map_some] at hc
    obtain ⟨⟨hb, hpop⟩, -⟩ := hc
    simp only [hb, Option.isSome_some, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, pure,
      Except.pure, ERel]
    have hs1 : fs1.size.toNat ≤ FlatShuffler.maxStackSize := by have := hfr.size; rw [hf0s] at this; omega
    have hn1 : fs1.targetSize.toNat ≤ FlatShuffler.maxStackSize := by rw [hfr.tsize, hf0n]; exact hn
    exact ⟨out_pop hpop hs1 hn1, by simp⟩
  | done =>
    simp only [FlatShuffler.Flat.absOut, Corr, SurplusRel, Option.map_none] at hc
    obtain ⟨⟨hb, hpop⟩, hcan⟩ := hc
    simp only [hb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    have hre : removeSurplus initial = .ok ⟨none, removed.state⟩ := by
      simpa only [← hb] using hr
    have htotal : ∀ i, (removed.state.mapping.destinationOf i).isSome := by
      simpa only [State.noSurplus, State.isSurplus, Option.isSome_iff_ne_none] using
        removeSurplus_noSurplus initial removed.state hre
    have hrbound' : removed.state.boundValue = initial.boundValue :=
      funext (removeSurplus_keeps_bindings initial removed.state hre)
    have hdom : ∀ j, (removed.state.mapping.symm j).isSome =
        (removed.state.planned_mapping.symm j).isSome := by
      intro j
      rw [← boundValue_isSome, hrbound', boundValue_isSome, hrplan]
    -- The list state of the flat state after `removeSurplus`.
    have hn1 : fs1.targetSize.toNat ≤ FlatShuffler.maxStackSize := by rw [hfr.tsize, hf0n]; exact hn
    have hsz1 : fs1.size.toNat ≤ FlatShuffler.maxStackSize := by have := hfr.size; rw [hf0s] at this; omega
    have he1 : e = FlatShuffler.Flat.listEnv fs1.targetSize.toNat fs1.target fs1.spills := by
      rw [hfr.tsize, hfr.target, hfr.spills, hf0n, hf0t, hf0p]; exact he
    have hrel1 := listOf_rel hn1 hsz1 hpop.mapping htotal he1 hpop.stack.symm hpop.trace
      hpop.pend.symm hcan hct
    have hs1 := listOf_sim hn1 hsz1 hpop.mapping htotal he1
    -- The planned mapping as a list.
    let pl := (M.pos.toList.take n.toNat).map optOf
    have hpl0 : pl = (absP P).pos := by rw [← hP]; rfl
    have hplc : PlanCorr removed.state pl := by
      intro j
      rw [hpl0, hrplan]
      simp only [absP, Mapping.positionOf, initial]
      rw [List.getElem?_eq_getElem (by simpa using j.isLt)]
      simp
    have hplr : FlatShuffler.Flat.PlanR fs1.targetSize.toNat M.pos pl := by
      intro d hd
      rw [hfr.tsize, hf0n] at hd
      have hpd : pl[d.toNat]? = some (optOf (get M.pos d)) := by
        simp [pl, hd, FlatShuffler.Flat.get_toNat _ (show d.toNat < FlatShuffler.maxStackSize by omega)]
        refine ⟨_, ?_, rfl⟩
        simp [show d.toNat < FlatShuffler.maxStackSize by omega]
      rw [hpd, Option.join_some]
      simp [optOf]
    have hl1 := hrel1.len
    have hdist : ∀ p < (listOf fs1).len, ∀ q < (listOf fs1).len,
        (listOf fs1).dest p = (listOf fs1).dest q → p = q := by
      intro p hp q hq h
      have hd := hrel1.dests
      have hdl := FlatShuffler.St.length_dests (listOf fs1)
      rw [FlatShuffler.St.dest_eq, FlatShuffler.St.dest_eq, getElem!_pos (listOf fs1).dests p (by omega),
        getElem!_pos (listOf fs1).dests q (by omega)] at h
      exact hd.2 p (by omega) q (by omega) h
    have hbound : ∀ q < (listOf fs1).len, FlatShuffler.isHole pl ((listOf fs1).dest q) = false := by
      intro q hq
      obtain ⟨j, hj, hjd⟩ := hrel1.mapping ⟨q, by omega⟩
      have hs : (removed.state.mapping.symm j).isSome = true := by
        rw [(removed.state.mapping.eq_some_iff).mpr hj]; rfl
      have hp := hplc j
      simp only [Mapping.positionOf] at hp
      rw [← hdom j, hs] at hp
      unfold FlatShuffler.isHole
      rw [show (listOf fs1).dest q = j.val from hjd.symm]
      simp [hp]
    have hlow := FlatShuffler.Flat.lowOk_of (pl := pl) hdist hbound hs1 hplr
    have hsr := FlatShuffler.Flat.sim_lowest hs1 hplr hlow l
    have hlc := lowest_corr hrel1 hplc
    obtain ⟨permuted, hp, hlength, hpplan, hppending, hpbound, -⟩ :=
      PermuteAtLowestHeight.permuteAtLowestHeight_result_spec removed.state htotal hdom
    rw [hp] at hlc
    have herel := erel_of hsr hlc
    rw [hp, except_ok_bind]
    generalize FlatShuffler.Flat.permuteAtLowestHeight M.pos l fs1 = r2 at hsr herel ⊢
    generalize FlatShuffler.lowest e.n pl (listOf fs1) = mres at hsr hlc
    rcases mres with (_ | _) | st2 <;>
      simp only [ResCorr, FlatShuffler.Flat.SimR] at hsr hlc
    · simp only [hlc.1, hsr.1, Option.isSome_some, ↓reduceIte, reduceCtorEq,
        not_false_eq_true]
      exact herel
    obtain ⟨hpb, hrel2⟩ := hlc
    obtain ⟨s2, fs2⟩ := r2
    obtain ⟨hs2d, hs2⟩ := hsr
    dsimp only at hs2d hs2
    subst hs2d
    simp only [hpb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, not_true_eq_false]
    have hbound' : permuted.state.boundValue = initial.boundValue := hpbound.trans hrbound'
    have hsize : permuted.state.stack.length + permuted.state.pending_generations =
        (decodedTargetStack e).length := by
      rw [hlength, hppending, hrpending]
      have hcount := unmapped_of_boundValue_eq initial removed.state hrbound'
      simpa only [initial, ← hcount] using Mapping.total_size removed.state.mapping htotal
    have hpending :
        permuted.state.mapping.unmapped_target_slots = permuted.state.pending_generations := by
      rw [unmapped_of_boundValue_eq initial permuted.state hbound', hppending, hrpending]
    rw [requires_of_true _ hsize, except_ok_bind, requires_of_true _ hpending, except_ok_bind]
    simp only [size_ok hs2 hrel2 hsize, unmapped_ok hs2 hrel2 hpending, not_true_eq_false,
      ↓reduceIte]
    by_cases hav : ∀ i, permuted.state.isAvailable i
    · rw [requires_of_true _ hav, except_ok_bind]
      simp only [(avail_iff hs2 hrel2).mpr hav, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlab : ∀ j : Fin (decodedTargetStack e).length,
          ((decodedTargetStack e)[j.val]'j.isLt).isFunctionReturnLabel → (permuted.state.mapping.symm j).isSome
      · rw [requires_of_true _ hlab, except_ok_bind]
        simp only [(labels_iff hs2 hrel2).mpr hlab, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact bbu_erel hs2 hrel2 _
      · rw [requires_of_false _ hlab, except_error_bind]
        have hf : FlatShuffler.Flat.labelsFrom fs2 0 = false :=
          Bool.eq_false_iff.mpr fun h => hlab ((labels_iff hs2 hrel2).mp h)
        simp only [hf, Bool.not_false, ↓reduceIte, ERel]
    · rw [requires_of_false _ hav, except_error_bind]
      have hf : FlatShuffler.Flat.availableFrom fs2 0 = false :=
        Bool.eq_false_iff.mpr fun h => hav ((avail_iff hs2 hrel2).mp h)
      simp only [hf, Bool.not_false, ↓reduceIte, ERel]

end ShufflerBridge.Planner
