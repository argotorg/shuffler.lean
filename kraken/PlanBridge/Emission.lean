import PlanBridge.List
import PlanBridge.Loops
import PlanBridge.Frame
import Shuffler.Emission.Run.Lemmas.Execution

/-!
The flat `emissionRun` and PR31 `Emission.run` (`emissionRun_erel`). The checks of `run` after
`permuteAtLowestHeight` give the same result on the two sides (`avail_iff`, `labels_iff`), and
`buildBottomUp` too (`bbu_erel`).
-/

namespace PlanBridge

open Shuffler Shuffler.Emission BbuBridge
open Bbu.Flat (get optOf optW absMapping NONE)

theorem requires_of_false (c : Prop) [Decidable c] (h : ¬c) (r : String) :
    requires c r = .error (.assertion r) := by
  simp only [requires, dite_eq_right h]; rfl

section
variable {e : Bbu.Env} {source : Stack} {fs : Bbu.Flat.St} {st : Bbu.St}
  {state : OState e source}

/-! ## The checks -/

theorem avail_one (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state) (i : Fin (tgt e).length) :
    Bbu.Flat.isAvailable fs (BitVec.ofNat 64 i.val) = true ↔ state.isAvailable i := by
  have hn := hs.n
  have hle := hs.n_le
  have htl := tgt_length e
  have hw : (BitVec.ofNat 64 i.val).toNat = i.val := Bbu.Flat.toNat_ofNat_lt (by omega)
  have ht := hs.target (t := BitVec.ofNat 64 i.val) (by rw [hw]; omega)
  rw [hw] at ht
  have hv : (tgt e)[i.val] = decode e.target[i.val]! := tgt_get e i.val i.isLt
  have hc := h.canonTarget i.val
  have hcopy := h.shallowestCopyPosition hc
  have hlen := h.len
  have hx : ∀ p, Bbu.shallowestCopyPosition st e.target[i.val]! = some p → p < 2 ^ 64 - 1 := by
    intro p hp
    rw [← hcopy] at hp
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hp
    have := q.isLt
    have := hs.len_lt
    unfold Bbu.MAX_N at this
    omega
  unfold Bbu.Flat.isAvailable State.isAvailable
  dsimp only
  rw [← ht, Bbu.Flat.sim_copy hs, ← hs.isSpilled, Fin.getElem_fin, hv]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [Bbu.Flat.optW_ne_NONE hx, isFree_iff,
    isSpilled_iff e source _ (List.mem_append_right _ (hv ▸ List.getElem_mem i.isLt)), ← hcopy,
    Option.isSome_map, or_assoc]

theorem avail_iff (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state) :
    Bbu.Flat.availableFrom fs 0 = true ↔ ∀ i, state.isAvailable i := by
  have hn := hs.n
  have htl := tgt_length e
  rw [Bbu.Flat.availableFrom_iff fs hs.n_le]
  constructor
  · intro hall i
    exact (avail_one hs h i).mp (hall i.val (by omega))
  · intro hall d hd
    exact (avail_one hs h ⟨d, by omega⟩).mpr (hall _)

theorem labels_one (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state) (j : Fin (tgt e).length) :
    ((get fs.target (BitVec.ofNat 64 j.val)).kind ≠ Bbu.FunctionReturnLabel
        || get fs.pos (BitVec.ofNat 64 j.val) ≠ NONE) = true ↔
      ((tgt e)[j.val].isFunctionReturnLabel → (state.mapping.symm j).isSome) := by
  have hn := hs.n
  have hle := hs.n_le
  have htl := tgt_length e
  have hw : (BitVec.ofNat 64 j.val).toNat = j.val := Bbu.Flat.toNat_ofNat_lt (by omega)
  have ht := hs.target (t := BitVec.ofNat 64 j.val) (by rw [hw]; omega)
  rw [hw] at ht
  have hp := hs.pos_ne_NONE (d := BitVec.ofNat 64 j.val) (by rw [hw]; omega)
  rw [hw, ← h.positionOf j, Option.isSome_map] at hp
  rw [← ht, tgt_get e j.val j.isLt, isFRL_iff (h.canonTarget j.val)]
  simp only [Mapping.positionOf] at hp
  by_cases hk : e.target[j.val]!.kind = Bbu.FunctionReturnLabel
  · simp only [hk, ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq,
      forall_const, hp]
  · simp only [hk, ne_eq, not_false_eq_true, decide_true, Bool.true_or, false_implies]

theorem labels_iff (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state) :
    Bbu.Flat.labelsFrom fs 0 = true ↔ ∀ j : Fin (tgt e).length,
      ((tgt e)[j.val]'j.isLt).isFunctionReturnLabel → (state.mapping.symm j).isSome := by
  have hn := hs.n
  have htl := tgt_length e
  rw [Bbu.Flat.labelsFrom_iff fs hs.n_le]
  constructor
  · intro hall j
    exact (labels_one hs h j).mp (hall j.val (by omega))
  · intro hall d hd
    exact (labels_one hs h ⟨d, by omega⟩).mpr (hall _)

-- The size check passes on both sides.
theorem size_ok (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state)
    (hsize : state.stack.length + state.pending_generations = (tgt e).length) :
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
  unfold Bbu.MAX_N at hle
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

-- The count check passes on both sides.
theorem unmapped_ok (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state)
    (hpending : state.mapping.unmapped_target_slots = state.pending_generations) :
    Bbu.Flat.unmappedFrom fs 0 0 = fs.pend := by
  have hle := hs.n_le
  have hmap := (out_of hs h).map
  simp only [absMapping, absP, Bbu.Map.Mapping.mk.injEq] at hmap
  rw [Bbu.Flat.unmappedFrom_eq fs hle, Bbu.Flat.countP_none' _ _ hle, hmap.2]
  have hc := absP_count state.mapping
  simp only [absP] at hc
  rw [hc, hpending, h.pendingGenerations, ← hs.pend, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## `buildBottomUp` -/

theorem bbu_erel (hs : Bbu.Flat.Sim e fs st) (h : Rel e st state) (hv : state.Valid) :
    ERel (Bbu.Flat.buildBottomUp fs) (buildBottomUp state hv) := by
  have hn := hs.n
  have htl := tgt_length e
  have hi : Bbu.InvS e st 0 := by
    refine ⟨?_, hs.n ▸ hs.n_le, Nat.zero_le _, h.pos⟩
    have := hv.1
    rw [h.len, h.pendingGenerations, htl] at this
    exact this
  have hl := Bbu.Flat.sim_loop (Bbu.Flat.permR e) fs st 0 hs hi (Nat.zero_le _)
  rw [buildBottomUp_eq_post]
  exact erel_of hl (loop_corr' e source st state 0 h)

end
/-! ## `Emission::run` -/

-- The members of the constructor state that the loop on `m_pendingGenerations` does not write.
theorem ctorP_fields (data : Vector Bbu.StackSlot Bbu.MAX_N) (m : Bbu.Word)
    (target : Vector Bbu.StackSlot Bbu.MAX_N) (n : Bbu.Word) (M : Bbu.Flat.Mapping)
    (spills : BitVec 32 → BitVec 8) (u : Bbu.Flat.Uninit) :
    let fs := Bbu.Flat.ctorP data m target n M spills u
    fs.size = m ∧ fs.target = target ∧ fs.targetSize = n ∧ fs.spills = spills ∧ fs.data = data := by
  unfold Bbu.Flat.ctorP
  dsimp only
  rw [Bbu.Flat.pend_fold]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem out_pop {e : Bbu.Env} {source : Stack} {fs : Bbu.Flat.St} {state : OState e source}
    {A : Bbu.Map.Mapping} (h : PopRel (Bbu.Flat.absSt A fs) state) (hs : fs.size.toNat ≤ Bbu.MAX_N)
    (ht : fs.targetSize.toNat ≤ Bbu.MAX_N) : Out fs state :=
  ⟨h.mapping, h.stack.symm, h.trace, hs, ht⟩

theorem emissionRun_erel (data target : Vector Bbu.StackSlot Bbu.MAX_N) (m n : Bbu.Word)
    (hm : m.toNat ≤ Bbu.MAX_N) (hn : n.toNat ≤ Bbu.MAX_N) (M : Bbu.Flat.Mapping)
    (spills : BitVec 32 → BitVec 8) (u : Bbu.Flat.Uninit) (l : Bbu.Flat.Locals) {e : Bbu.Env}
    (he : e = Bbu.Flat.listEnv n.toNat target spills)
    (P : Mapping ((data.toList.take m.toNat).map decode).length (tgt e).length)
    (hP : absMapping M.dest M.pos m n = absP P)
    (hcs : ∀ v ∈ data.toList.take m.toNat, Canon v) (hct : ∀ v ∈ e.target, Canon v) :
    ERel (Bbu.Flat.emissionRun M.pos l (Bbu.Flat.ctorP data m target n M spills u))
      (Emission.run ((data.toList.take m.toNat).map decode) (tgt e) P
        (spillSet e ((data.toList.take m.toNat).map decode))) := by
  obtain ⟨hf0s, hf0t, hf0n, hf0p, hf0d⟩ := ctorP_fields data m target n M spills u
  generalize hfs0 : Bbu.Flat.ctorP data m target n M spills u = fs0 at hf0s hf0t hf0n hf0p hf0d
  have hA := Bbu.Flat.ctorP_abs data m target n M spills u hm hn
  rw [hfs0, hP] at hA
  have hrs := Bbu.Flat.removeSurplus_abs (absP P) fs0 (by rw [hf0s]; exact hm)
  rw [hA] at hrs
  let initial : OState e ((data.toList.take m.toNat).map decode) := {
    planned_mapping := P, stack := (data.toList.take m.toNat).map decode,
    trace := .Lit _, mapping := P, pending_generations := P.unmapped_target_slots }
  have hc := removeSurplus_corr_canon (init_rel (target := tgt e)
    (spills := spillSet e ((data.toList.take m.toNat).map decode)) _ P) hcs
  rw [hrs] at hc
  change Corr _ _ (removeSurplus initial) at hc
  obtain ⟨removed, hr⟩ := removeSurplus_ok initial
  obtain ⟨hrplan, hrpending, -⟩ := removeSurplus_frame initial hr
  have hfr := Bbu.Flat.removeSurplus_frame fs0
  unfold Emission.run Bbu.Flat.emissionRun
  change ERel _ (removeSurplus initial >>= _)
  rw [hr, except_ok_bind]
  rw [hr] at hc
  generalize Bbu.Flat.removeSurplus fs0 = r1 at hc hfr ⊢
  obtain ⟨s1, fs1⟩ := r1
  dsimp only at hfr ⊢
  cases s1 with
  | assertionFailed => exact hc.elim
  | blocked =>
    simp only [Bbu.Flat.absOut, Corr, SurplusRel, Option.map_some] at hc
    obtain ⟨⟨hb, hpop⟩, -⟩ := hc
    simp only [hb, Option.isSome_some, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, pure,
      Except.pure, ERel]
    have hs1 : fs1.size.toNat ≤ Bbu.MAX_N := by have := hfr.size; rw [hf0s] at this; omega
    have hn1 : fs1.targetSize.toNat ≤ Bbu.MAX_N := by rw [hfr.tsize, hf0n]; exact hn
    exact ⟨out_pop hpop hs1 hn1, by simp⟩
  | done =>
    simp only [Bbu.Flat.absOut, Corr, SurplusRel, Option.map_none] at hc
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
    have hn1 : fs1.targetSize.toNat ≤ Bbu.MAX_N := by rw [hfr.tsize, hf0n]; exact hn
    have hsz1 : fs1.size.toNat ≤ Bbu.MAX_N := by have := hfr.size; rw [hf0s] at this; omega
    have he1 : e = Bbu.Flat.listEnv fs1.targetSize.toNat fs1.target fs1.spills := by
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
    have hplr : Bbu.Flat.PlanR fs1.targetSize.toNat M.pos pl := by
      intro d hd
      rw [hfr.tsize, hf0n] at hd
      have hpd : pl[d.toNat]? = some (optOf (get M.pos d)) := by
        simp [pl, hd, Bbu.Flat.get_toNat _ (show d.toNat < Bbu.MAX_N by omega)]
        refine ⟨_, ?_, rfl⟩
        simp [show d.toNat < Bbu.MAX_N by omega]
      rw [hpd, Option.join_some]
      simp [optOf]
    have hl1 := hrel1.len
    have hdist : ∀ p < (listOf fs1).len, ∀ q < (listOf fs1).len,
        (listOf fs1).dest p = (listOf fs1).dest q → p = q := by
      intro p hp q hq h
      have hd := hrel1.dests
      have hdl := Bbu.St.length_dests (listOf fs1)
      rw [Bbu.St.dest_eq, Bbu.St.dest_eq, getElem!_pos (listOf fs1).dests p (by omega),
        getElem!_pos (listOf fs1).dests q (by omega)] at h
      exact hd.2 p (by omega) q (by omega) h
    have hbound : ∀ q < (listOf fs1).len, Bbu.isHole pl ((listOf fs1).dest q) = false := by
      intro q hq
      obtain ⟨j, hj, hjd⟩ := hrel1.mapping ⟨q, by omega⟩
      have hs : (removed.state.mapping.symm j).isSome = true := by
        rw [(removed.state.mapping.eq_some_iff).mpr hj]; rfl
      have hp := hplc j
      simp only [Mapping.positionOf] at hp
      rw [← hdom j, hs] at hp
      unfold Bbu.isHole
      rw [show (listOf fs1).dest q = j.val from hjd.symm]
      simp [hp]
    have hlow := Bbu.Flat.lowOk_of (pl := pl) hdist hbound hs1 hplr
    have hsr := Bbu.Flat.sim_lowest hs1 hplr hlow l
    have hlc := lowest_corr hrel1 hplc
    obtain ⟨permuted, hp, hlength, hpplan, hppending, hpbound, -⟩ :=
      PermuteAtLowestHeight.permuteAtLowestHeight_result_spec removed.state htotal hdom
    rw [hp] at hlc
    have herel := erel_of hsr hlc
    rw [hp, except_ok_bind]
    generalize Bbu.Flat.permuteAtLowestHeight M.pos l fs1 = r2 at hsr herel ⊢
    generalize Bbu.lowest e.n pl (listOf fs1) = mres at hsr hlc
    rcases mres with (_ | _) | st2 <;>
      simp only [ResCorr, Bbu.Flat.SimR] at hsr hlc
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
        (tgt e).length := by
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
      by_cases hlab : ∀ j : Fin (tgt e).length,
          ((tgt e)[j.val]'j.isLt).isFunctionReturnLabel → (permuted.state.mapping.symm j).isSome
      · rw [requires_of_true _ hlab, except_ok_bind]
        simp only [(labels_iff hs2 hrel2).mpr hlab, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact bbu_erel hs2 hrel2 _
      · rw [requires_of_false _ hlab, except_error_bind]
        have hf : Bbu.Flat.labelsFrom fs2 0 = false :=
          Bool.eq_false_iff.mpr fun h => hlab ((labels_iff hs2 hrel2).mp h)
        simp only [hf, Bool.not_false, ↓reduceIte, ERel]
    · rw [requires_of_false _ hav, except_error_bind]
      have hf : Bbu.Flat.availableFrom fs2 0 = false :=
        Bool.eq_false_iff.mpr fun h => hav ((avail_iff hs2 hrel2).mp h)
      simp only [hf, Bool.not_false, ↓reduceIte, ERel]

end PlanBridge
