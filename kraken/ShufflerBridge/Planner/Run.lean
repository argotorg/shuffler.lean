module

public import ShufflerBridge.Planner.ResolveLoop
import all ShufflerBridge.Planner.ResolveLoop
public import ShufflerBridge.Planner.Bounded
import all ShufflerBridge.Planner.Bounded

@[expose] public section

/-!
The flat `runLoop` and PR31 `Planner.run.loop` (`runLoop_corr`).
-/

namespace ShufflerBridge.Planner

open Shuffler Shuffler.Planner ShufflerBridge.Emission
open FlatShuffler.Flat (get put optOf NONE ofNat_succ)

/-! ## The loops of `run` -/

theorem take_eq_of_get {α : Type} [Inhabited α] {a b : Vector α FlatShuffler.maxStackSize} {k : Nat}
    (hk : k ≤ FlatShuffler.maxStackSize) (h : ∀ i < k, get a (.ofNat 64 i) = get b (.ofNat 64 i)) :
    a.toList.take k = b.toList.take k := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.length_take, Vector.length_toList] at h1
  have := h i (by omega)
  rw [FlatShuffler.Flat.get_ofNat a (by omega), FlatShuffler.Flat.get_ofNat b (by omega)] at this
  simpa using this

theorem copyFrom_get (pl : FlatShuffler.Flat.Planner) (hm : pl.sourceSize.toNat ≤ FlatShuffler.maxStackSize) :
    ∀ j k (data : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize), k + j = pl.sourceSize.toNat → ∀ i, i < pl.sourceSize.toNat →
      (i < k → get data (.ofNat 64 i) = get pl.source (.ofNat 64 i)) →
      get (FlatShuffler.Flat.copyFrom pl (.ofNat 64 k) data) (.ofNat 64 i) = get pl.source (.ofNat 64 i) := by
  intro j
  induction j with
  | zero =>
    intro k data hk i hi h
    rw [FlatShuffler.Flat.copyFrom, dite_eq_right (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega)]
    exact h (by omega)
  | succ j ih =>
    intro k data hk i hi h
    rw [FlatShuffler.Flat.copyFrom, dite_eq_left (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega),
      ofNat_succ]
    refine ih (k + 1) _ (by omega) i hi (fun hik => ?_)
    rw [get_put _ (by omega) (by omega)]
    by_cases hik' : i = k
    · rw [ite_eq_left hik', hik']
    · rw [ite_eq_right hik']; exact h (by omega)

-- The source slots of `copyFrom`.
theorem take_copyFrom (pl : FlatShuffler.Flat.Planner) (hm : pl.sourceSize.toNat ≤ FlatShuffler.maxStackSize)
    (data : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) :
    (FlatShuffler.Flat.copyFrom pl 0 data).toList.take pl.sourceSize.toNat = pl.source.toList.take pl.sourceSize.toNat :=
  take_eq_of_get hm fun i hi =>
    copyFrom_get pl hm pl.sourceSize.toNat 0 data (by omega) i hi (fun h => absurd h (by omega))

theorem sourcesFrom_get (n : FlatShuffler.Word) (hn : n.toNat ≤ FlatShuffler.maxStackSize) (M : FlatShuffler.Flat.Mapping) :
    ∀ j k (srcs : Vector FlatShuffler.Word FlatShuffler.maxStackSize), k + j = n.toNat → ∀ i, i < n.toNat →
      (i < k → get srcs (.ofNat 64 i) = get M.pos (.ofNat 64 i)) →
      get (FlatShuffler.Flat.sourcesFrom n (.ofNat 64 k) M srcs) (.ofNat 64 i) = get M.pos (.ofNat 64 i) := by
  intro j
  induction j with
  | zero =>
    intro k srcs hk i hi h
    rw [FlatShuffler.Flat.sourcesFrom, dite_eq_right (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega)]
    exact h (by omega)
  | succ j ih =>
    intro k srcs hk i hi h
    rw [FlatShuffler.Flat.sourcesFrom, dite_eq_left (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega),
      ofNat_succ]
    refine ih (k + 1) _ (by omega) i hi (fun hik => ?_)
    rw [get_put _ (by omega) (by omega)]
    by_cases hik' : i = k
    · rw [ite_eq_left hik', hik']
    · rw [ite_eq_right hik']; exact h (by omega)

theorem droppedFrom_toNat (m : FlatShuffler.Word) (hm : m.toNat ≤ FlatShuffler.maxStackSize) (d : Vector (BitVec 8) FlatShuffler.maxStackSize) :
    ∀ j k c, k + j = m.toNat → c ≤ k →
      (FlatShuffler.Flat.droppedFrom m d (.ofNat 64 k) (.ofNat 64 c)).toNat =
        c + (List.range' k j).countP fun i => get d (.ofNat 64 i) ≠ 0 := by
  intro j
  induction j with
  | zero =>
    intro k c hk hc
    rw [FlatShuffler.Flat.droppedFrom, dite_eq_right (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold FlatShuffler.maxStackSize at *; omega)]
    simp
  | succ j ih =>
    intro k c hk hc
    rw [FlatShuffler.Flat.droppedFrom, dite_eq_left (by rw [FlatShuffler.Flat.ofNat_lt_iff (by omega)]; omega),
      ofNat_succ, List.range'_succ, List.countP_cons]
    by_cases h : get d (.ofNat 64 k) ≠ 0
    · rw [ite_eq_left h, ofNat_succ, ih (k + 1) (c + 1) (by omega) (by omega)]
      simp only [ne_eq, decide_not, h]
      simp; omega
    · rw [ite_eq_right h, ih (k + 1) c (by omega) (by omega)]
      simp only [ne_eq, Decidable.not_not] at h
      simp [h]

-- The flat count of the dropped bytes is the PR31 count.
theorem droppedCount_eq {m : FlatShuffler.Word} (hm : m.toNat ≤ FlatShuffler.maxStackSize) {k : Nat} (hk : k = m.toNat)
    {dn : Vector Byte k} {d : Vector (BitVec 8) FlatShuffler.maxStackSize} (h : DnR dn d) :
    (FlatShuffler.Flat.droppedCount m d).toNat =
      (Finset.univ.filter (fun i : Fin k => dn[i] ≠ 0)).card := by
  rw [FlatShuffler.Flat.droppedCount, show (0 : FlatShuffler.Word) = .ofNat 64 0 from rfl,
    droppedFrom_toNat m hm d m.toNat 0 0 (by omega) (by omega), Nat.zero_add,
    ← List.toFinset_finRange, (List.nodup_finRange k).card_eq_countP, ← List.range_eq_range',
    ← hk, ← List.map_coe_finRange_eq_range, List.countP_map]
  congr 1
  funext i
  simp only [Function.comp, ne_eq, decide_eq_decide]
  rw [h.zero i]

-- The PR31 dropped bytes as a list.
theorem toList_eq_drops {m : FlatShuffler.Word} (hm : m.toNat ≤ FlatShuffler.maxStackSize) {k : Nat} (hk : k = m.toNat)
    {dn : Vector Byte k} {d : Vector (BitVec 8) FlatShuffler.maxStackSize} (h : DnR dn d) :
    dn.toList = drops d m := by
  apply List.ext_getElem (by rw [drops_length hm]; simp [hk])
  intro i h1 _
  simp only [Vector.length_toList] at h1
  rw [Vector.getElem_toList, show dn[i] = dn[(⟨i, h1⟩ : Fin k)] from rfl, h ⟨i, h1⟩]
  simp only [drops, List.getElem_map, List.getElem_take, Vector.getElem_toList]
  rw [FlatShuffler.Flat.get_ofNat d (by omega)]

-- The converse of `mapR_abs`.
theorem mapR_of_abs {M : FlatShuffler.Flat.Mapping} {m n : FlatShuffler.Word} (hm : m.toNat ≤ FlatShuffler.maxStackSize)
    (hn : n.toNat ≤ FlatShuffler.maxStackSize) {s t : Nat} (hs : s = m.toNat) (ht : t = n.toNat) {P : Mapping s t}
    (h : FlatShuffler.Flat.absMapping M.dest M.pos m n = absP P) : MapR M P := by
  subst hs ht
  simp only [FlatShuffler.Flat.absMapping, absP, FlatShuffler.Map.Mapping.mk.injEq] at h
  constructor
  · intro i
    have := List.getElem_of_eq h.1 (i := i.val) (by simp; omega)
    simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList,
      List.getElem_finRange] at this
    rw [FlatShuffler.Flat.get_ofNat _ (by omega)]
    exact this
  · intro j
    have := List.getElem_of_eq h.2 (i := j.val) (by simp; omega)
    simp only [List.getElem_map, List.getElem_take, Vector.getElem_toList,
      List.getElem_finRange] at this
    rw [FlatShuffler.Flat.get_ofNat _ (by omega)]
    exact this

/-! ## `Emission.run` -/

-- An `ok` result of PR31 `Emission.run` keeps the planned mapping.
theorem run_planned {source target : Stack} {P : Mapping source.length target.length}
    {spills : SpillSet} {res : Emission.Result source target spills}
    (h : Emission.run source target P spills = .ok res) : res.state.planned_mapping = P := by
  let initial : Emission.State source target spills := {
    planned_mapping := P, stack := source, trace := .Lit source,
    mapping := P, pending_generations := P.unmapped_target_slots }
  obtain ⟨removed, hr⟩ := Emission.removeSurplus_ok initial
  obtain ⟨hrplan, -, -⟩ := Emission.removeSurplus_frame initial hr
  unfold Emission.run at h
  change (Emission.removeSurplus initial >>= _) = _ at h
  rw [hr, except_ok_bind] at h
  cases hblocked : removed.blocked with
  | some b =>
    simp only [hblocked, Option.isSome_some, ↓reduceIte] at h
    cases h
    exact hrplan
  | none =>
    simp only [hblocked, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
    have hre : Emission.removeSurplus initial = .ok ⟨none, removed.state⟩ := by
      simpa only [← hblocked] using hr
    have htotal : ∀ i, (removed.state.mapping.destinationOf i).isSome := by
      simpa only [Emission.State.noSurplus, Emission.State.isSurplus,
        Option.isSome_iff_ne_none] using Emission.removeSurplus_noSurplus initial removed.state hre
    have hrbound' : removed.state.boundValue = initial.boundValue :=
      funext (Emission.removeSurplus_keeps_bindings initial removed.state hre)
    have hdom : ∀ j, (removed.state.mapping.symm j).isSome =
        (removed.state.planned_mapping.symm j).isSome := by
      intro j
      rw [← Emission.boundValue_isSome, hrbound', Emission.boundValue_isSome, hrplan]
    obtain ⟨permuted, hp, -, hpplan, -, -, -⟩ :=
      Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight_result_spec removed.state htotal hdom
    rw [hp, except_ok_bind] at h
    cases hpb : permuted.blocked with
    | some b =>
      simp only [hpb, Option.isSome_some, ↓reduceIte] at h
      cases h
      exact hpplan.trans hrplan
    | none =>
      simp only [hpb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
      simp only [requires] at h
      split at h
      · split at h
        · split at h
          · split at h
            · simp only [pure_bind] at h
              exact (Emission.buildBottomUp_frame _ _ h).1.trans (hpplan.trans hrplan)
            · cases h
          · cases h
        · cases h
      · cases h


-- `emissionRun_erel` for a source `src` that the first `m` slots of `data` decodeStackSlot to.
theorem emissionRun_erel' (data target : Vector FlatShuffler.StackSlot FlatShuffler.maxStackSize) (m n : FlatShuffler.Word)
    (hm : m.toNat ≤ FlatShuffler.maxStackSize) (hn : n.toNat ≤ FlatShuffler.maxStackSize) (M : FlatShuffler.Flat.Mapping)
    (spills : BitVec 32 → BitVec 8) (u : FlatShuffler.Flat.Uninit) (l : FlatShuffler.Flat.Locals) {e : FlatShuffler.Env}
    (he : e = FlatShuffler.Flat.listEnv n.toNat target spills) {src : Stack}
    (hsrc : (data.toList.take m.toNat).map decodeStackSlot = src) (P : Mapping src.length (decodedTargetStack e).length)
    (hP : FlatShuffler.Flat.absMapping M.dest M.pos m n = absP P)
    (hcs : ∀ v ∈ data.toList.take m.toNat, StackSlotHasCanonicalEncoding v) (hct : ∀ v ∈ e.target, StackSlotHasCanonicalEncoding v) :
    ERel (FlatShuffler.Flat.emissionRun M.pos l (FlatShuffler.Flat.ctorP data m target n M spills u))
      (Emission.run src (decodedTargetStack e) P (spilledVariables e src)) := by
  subst hsrc
  exact emissionRun_erel data target m n hm hn M spills u l he P hP hcs hct

/-! ## The loop of `Planner::run` -/

-- The flat result `r` of `runLoop` and a PR31 result of `Planner.run.loop`. For `.done`, the
-- flat buffers hold the stack, the trace and the sources of the planned mapping.
def RunR (pl : FlatShuffler.Flat.Planner) (r : FlatShuffler.Flat.Status × FlatShuffler.Flat.PSt) :
    Except ShuffleErr (Planner.Result (srcOf pl.source pl.sourceSize) (srcOf pl.target pl.targetSize)) → Prop
  | .error _ => r.1 = .assertionFailed
  | .ok res => SRpl pl r.2.spills r.2.dropped res.state ∧ r.2.saw = res.sawWildcardCopy ∧
    match res.result with
    | none => r.1 = .blocked
    | some st => r.1 = .done ∧ (r.2.data.toList.take st.stack.length).map decodeStackSlot = st.stack ∧
        r.2.trace = (traceOperations st.trace).map encodeTraceOperation ∧
        ∀ j : Fin (srcOf pl.target pl.targetSize).length,
          optOf (get r.2.sources (.ofNat 64 j.val)) = (st.planned_mapping.symm j).map Fin.val

theorem runLoop_corr {pl : FlatShuffler.Flat.Planner} (hm : pl.sourceSize.toNat ≤ FlatShuffler.maxStackSize)
    (hn : pl.targetSize.toNat ≤ FlatShuffler.maxStackSize)
    (ok : SlotsOk (pl.source.toList.take pl.sourceSize.toNat ++ pl.target.toList.take pl.targetSize.toNat))
    (take : Bool) (k : Nat) :
    ∀ (s : FlatShuffler.Flat.PSt) (cur : State (srcOf pl.source pl.sourceSize) (srcOf pl.target pl.targetSize)) (saw : Bool)
      (us : Nat → FlatShuffler.Flat.RunU), (pl.sourceSize - FlatShuffler.Flat.droppedCount pl.sourceSize s.dropped).toNat = k →
      SRpl pl s.spills s.dropped cur → s.saw = saw →
      RunR pl (FlatShuffler.Flat.runLoop pl take s us)
        (Planner.run.loop (srcOf pl.source pl.sourceSize) (srcOf pl.target pl.targetSize)
          (if take then .Take else .Leave) cur saw) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s cur saw us hk hinit hsaw
  have hsl := srcOf_length (v := pl.source) hm
  have htl := srcOf_length (v := pl.target) hn
  rcases cur with ⟨cspills, callowed, cdropped⟩
  obtain ⟨hsp, hal, hdn⟩ := hinit
  dsimp only at hsp hal hdn
  subst hsp
  rw [FlatShuffler.Flat.runLoop.eq_1, Planner.run.loop.eq_1]
  have hdr : cdropped.toList = drops s.dropped pl.sourceSize := toList_eq_drops hm hsl hdn
  simp only [hdr]
  have hbk := buildMapping_corr (b := ⟨pl.source, pl.sourceSize, pl.target, pl.targetSize, s.dropped, take⟩)
    ⟨hm, hn, fun i hi => ok.canon _ (List.mem_append_left _ (get_mem_take _ hm hi)),
      fun j hj => ok.canon _ (List.mem_append_right _ (get_mem_take _ hn hj))⟩
    (mapR_init (us 0).mapping hm hn hsl htl)
  generalize FlatShuffler.Flat.buildMapping _ _ = ob at hbk ⊢
  generalize BuildMapping.buildMapping _ _ _ _ = eb at hbk ⊢
  rcases ob with _ | ⟨M, sw⟩ <;> rcases eb with _ | bld <;> simp only [OptCorr] at hbk
  · rfl
  obtain ⟨hMR, hsw⟩ := hbk
  rw [except_ok_bind]
  dsimp only
  have hsrc : ((FlatShuffler.Flat.copyFrom pl 0 s.data).toList.take pl.sourceSize.toNat).map decodeStackSlot =
      srcOf pl.source pl.sourceSize := by
    rw [take_copyFrom pl hm]; rfl
  have hcs : ∀ v ∈ (FlatShuffler.Flat.copyFrom pl 0 s.data).toList.take pl.sourceSize.toNat, StackSlotHasCanonicalEncoding v := by
    rw [take_copyFrom pl hm]; exact fun v hv => ok.canon v (List.mem_append_left _ hv)
  have he : ERel (e := FlatShuffler.Flat.listEnv pl.targetSize.toNat pl.target s.spills) (source := srcOf pl.source pl.sourceSize)
      (FlatShuffler.Flat.emissionRun M.pos (us 0).l
      (FlatShuffler.Flat.ctorP (FlatShuffler.Flat.copyFrom pl 0 s.data) pl.sourceSize pl.target pl.targetSize M s.spills (us 0).u))
      (Emission.run (srcOf pl.source pl.sourceSize) (srcOf pl.target pl.targetSize) bld.mapping
        (pSpills (pl.source.toList.take pl.sourceSize.toNat) pl.targetSize.toNat pl.target s.spills)) :=
    emissionRun_erel' _ pl.target pl.sourceSize pl.targetSize hm hn M s.spills (us 0).u (us 0).l rfl hsrc bld.mapping
      (mapR_abs hm hn hsl htl hMR) hcs (fun v hv => ok.canon v (List.mem_append_right _ hv))
  generalize her : Emission.run _ _ bld.mapping _ = er at he ⊢
  generalize FlatShuffler.Flat.emissionRun _ _ _ = fr at he ⊢
  rcases er with _ | res
  · simp only [ERel] at he
    rw [except_error_bind]
    simp [RunR, he]
  obtain ⟨hout, hst⟩ := he
  rw [except_ok_bind]
  have hsz := hout.size_le
  have hl : res.state.stack.length = fr.2.size.toNat := by rw [← hout.stack]; simp; omega
  cases hbl : res.blocked with
  | none =>
    simp only [hbl] at hst ⊢
    simp only [hst, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, pure, Except.pure, RunR]
    refine ⟨⟨rfl, hal, hdn⟩, by rw [hsaw, hsw], trivial, by rw [hl]; exact hout.stack, hout.trace,
      fun j => ?_⟩
    rw [run_planned her, show (0 : FlatShuffler.Word) = .ofNat 64 0 from rfl,
      sourcesFrom_get pl.targetSize hn M pl.targetSize.toNat 0 s.sources (by omega) j (by omega)
        (fun h => absurd h (by omega))]
    exact hMR.pos j
  | some b =>
    simp only [hbl] at hst ⊢

    obtain ⟨hb1, hbo, hex⟩ := hst
    simp only [hb1, ne_eq, not_true_eq_false, ↓reduceIte]
    have htsz := hout.tsize_le
    have htl' : (srcOf pl.target pl.targetSize).length = fr.2.targetSize.toNat := by
      have := congrArg (fun x => x.pos.length) hout.map
      simp [FlatShuffler.Flat.absMapping, absP, FlatShuffler.Flat.listEnv] at this; omega
    have hC : MapR (⟨fr.2.dest, fr.2.pos⟩ : FlatShuffler.Flat.Mapping) res.state.mapping :=
      mapR_of_abs hsz htsz hl htl' hout.map
    have hr := resolve_corr hm hn ok
      (init := ⟨pSpills (pl.source.toList.take pl.sourceSize.toNat) pl.targetSize.toNat pl.target s.spills, callowed,
        cdropped⟩) (sp := s.spills) (dropped := s.dropped) ⟨rfl, hal, hdn⟩ hMR hC (csW := fr.2.size)
      hl.symm (by omega) (Emission.run_bounded her b hbl) hbo hex (us 0).r
    generalize FlatShuffler.Flat.resolve _ _ _ _ _ _ _ _ _ = q at hr ⊢
    generalize Planner.resolve _ _ _ _ = eq at hr ⊢
    rcases q with ⟨qr, qsp, qd⟩
    rcases eq with _ | ⟨succ, resolved⟩ <;> cases qr <;> simp only [RslvR] at hr
    · rw [except_error_bind]
      simp [RunR]
    · obtain ⟨rfl, hR⟩ := hr
      rw [except_ok_bind]
      simp only [not_true_eq_false, ↓reduceIte]
      have hc1 := droppedCount_eq hm hsl hR.2.2
      have hc0 := droppedCount_eq hm hsl hdn
      have hle1 := FlatShuffler.Flat.droppedCount_le pl.sourceSize qd
      have hle0 := FlatShuffler.Flat.droppedCount_le pl.sourceSize s.dropped
      by_cases hgt : FlatShuffler.Flat.droppedCount pl.sourceSize qd > FlatShuffler.Flat.droppedCount pl.sourceSize s.dropped
      · have hlt := BitVec.lt_def.mp hgt
        rw [dite_eq_left hgt, requires_of_true _ (by simp only [State.droppedCount]; omega),
          except_ok_bind]
        exact ih _ (by rw [← hk]; exact FlatShuffler.Flat.sub_lt_sub hle1 hle0 hgt) _ _ _ _ rfl hR
          (by simp only [hsaw, hsw])
      · have hlt := Nat.not_lt.mp fun h => hgt (BitVec.lt_def.mpr h)
        rw [dite_eq_right hgt, requires_of_false _ (by simp only [State.droppedCount]; omega),
          except_error_bind]
        rfl
    · obtain ⟨rfl, hR⟩ := hr
      rw [except_ok_bind]
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte, pure, Except.pure, RunR]
      exact ⟨hR, by rw [hsaw, hsw], trivial⟩

end ShufflerBridge.Planner
