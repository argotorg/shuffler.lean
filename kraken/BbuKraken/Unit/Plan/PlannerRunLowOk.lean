import BbuKraken.Unit.Plan.PlannerRunSurplus

namespace Bbu.Unit.PlannerRunU
open Flat

theorem ofNat_lt_word {i : Nat} {n : Word} (hn : n.toNat ≤ MAX_N) (hi : i < n.toNat) :
    BitVec.ofNat 64 i < n := by
  rw [BitVec.lt_def, Flat.toNat_ofNat_small (Nat.lt_of_lt_of_le hi hn)]
  exact hi

theorem MapInv.size_le {st : Flat.St}
    (h : MapInv st.size st.targetSize ⟨st.dest, st.pos⟩) (hn : HasNoSurplus st) :
    st.size.toNat ≤ st.targetSize.toNat := by
  let ds := (List.range st.size.toNat).map fun i => (get st.dest (BitVec.ofNat 64 i)).toNat
  have hd : ds.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := st.size.toNat))
    intro i j hi hj hij he
    have hi' := ofNat_lt_word h.m_bound (List.mem_range.mp hi)
    have hj' := ofNat_lt_word h.m_bound (List.mem_range.mp hj)
    have hw := h.dest_inj hi' hj' (hn _ hi') (BitVec.eq_of_toNat_eq he)
    have hwN := congrArg BitVec.toNat hw
    rw [Flat.toNat_ofNat_small (Nat.lt_of_lt_of_le (List.mem_range.mp hi) h.m_bound),
      Flat.toNat_ofNat_small (Nat.lt_of_lt_of_le (List.mem_range.mp hj) h.m_bound)] at hwN
    exact hij hwN
  have hb : ds ⊆ List.range st.targetSize.toNat := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have hi' := ofNat_lt_word h.m_bound (List.mem_range.mp hi)
    exact List.mem_range.mpr (BitVec.lt_def.mp ((h.dest _ hi').resolve_left (hn _ hi')))
  simpa only [ds, List.length_map, List.length_range] using hd.length_le_of_subset hb

def lowShape (fs : Flat.St) : Bbu.St :=
  ⟨(List.range fs.size.toNat).map (fun i => ⟨.junk, (get fs.dest (BitVec.ofNat 64 i)).toNat⟩),
    [], fs.pend.toNat, fs.trace⟩

theorem lowShape_len (fs : Flat.St) : (lowShape fs).len = fs.size.toNat := by
  simp only [lowShape, Bbu.St.len, List.length_map, List.length_range]

theorem lowShape_dest (fs : Flat.St) {i : Nat} (hi : i < fs.size.toNat) :
    (lowShape fs).dest i = (get fs.dest (BitVec.ofNat 64 i)).toNat := by
  simp [Bbu.St.dest, lowShape, List.getElem?_range hi]

def lowPlan (planned : Vector Word MAX_N) : List (Option Nat) :=
  planned.toList.map Flat.optOf

theorem lowPlanR (planned : Vector Word MAX_N) {n : Word} (hn : n.toNat ≤ MAX_N) :
    Flat.PlanR n.toNat planned (lowPlan planned) := by
  intro d hd
  have hm := Nat.lt_of_lt_of_le hd hn
  have he : ((lowPlan planned)[d.toNat]?).join = Flat.optOf (get planned d) := by
    simp only [lowPlan, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simpa using hm)]
    simp only [Option.map_some, Option.join_some, Vector.getElem_toList]
    rw [Flat.get_toNat planned hm]
  rw [he, Flat.optOf_eq_none]

theorem low_scan_step {planned : Vector Word MAX_N} {fs : Flat.St}
    (hm : fs.size.toNat ≤ MAX_N) {k : Nat} (hk : k < fs.size.toNat)
    {sc : Flat.Scan} (h : Flat.ScanInv (lowPlan planned) (lowShape fs) k sc) :
    Flat.ScanInv (lowPlan planned) (lowShape fs) (k + 1)
      (Flat.scanStep planned fs (.ofNat 64 k) (get fs.dest (.ofNat 64 k)) sc) := by
  have hkN : k < MAX_N := Nat.lt_of_lt_of_le hk hm
  have hkw := Flat.toNat_ofNat_small hkN
  have hdk := lowShape_dest fs hk
  have hH : (get planned (.ofNat 64 k) == NONE) = Bbu.isHole (lowPlan planned) k := by
    have hh := lowPlanR planned (n := fs.size) hm (.ofNat 64 k) (by rw [hkw]; exact hk)
    rw [hkw] at hh
    unfold Bbu.isHole
    rw [Bool.eq_iff_iff, beq_iff_eq, Option.isNone_iff_eq_none]
    exact hh
  have hP : decide (fs.size ≤ get fs.dest (.ofNat 64 k)) = Bbu.isParked (lowShape fs) k := by
    unfold Bbu.isParked
    rw [lowShape_len, hdk]
    exact decide_eq_decide.2 BitVec.le_def
  apply Flat.ScanInv.next hkN h <;>
    simp only [Flat.scanStep, Flat.lowHole, Flat.lowPark, Flat.lowSets, Flat.lowVal, hH, hP] <;>
    cases b1 : Bbu.isParked (lowShape fs) k <;> cases b2 : Bbu.isHole (lowPlan planned) k <;>
    simp
  all_goals first | exact ⟨_, hdk.symm, rfl⟩ | exact ⟨_, hkw, rfl⟩

theorem low_scan_spec {planned : Vector Word MAX_N} {fs : Flat.St}
    (h : MapInv fs.size fs.targetSize ⟨fs.dest, fs.pos⟩) (hn : HasNoSurplus fs) :
    ∀ d k sc, k + d = fs.size.toNat →
      Flat.ScanInv (lowPlan planned) (lowShape fs) k sc →
      ∃ sc', Flat.scan planned fs (.ofNat 64 k) sc = some sc' ∧
        Flat.ScanInv (lowPlan planned) (lowShape fs) fs.size.toNat sc'
  | 0, k, sc, hd, hs => by
    refine ⟨sc, ?_, by simpa only [Nat.add_zero] using hd ▸ hs⟩
    rw [Flat.scan, dite_eq_right]
    have hkN : k ≤ MAX_N := by have hm := h.m_bound; omega
    have hkw : (BitVec.ofNat 64 k).toNat = k :=
      Flat.toNat_ofNat_of_lt (by have hN : MAX_N = 1024 := rfl; omega)
    rw [BitVec.lt_def, hkw]
    omega
  | d + 1, k, sc, hd, hs => by
    have hk : k < fs.size.toNat := by omega
    have hkN := Nat.lt_of_lt_of_le hk h.m_bound
    have hkw := Flat.toNat_ofNat_small hkN
    obtain ⟨sc', he, hi⟩ := low_scan_spec h hn d (k + 1) _ (by omega)
      (low_scan_step h.m_bound hk hs)
    refine ⟨sc', ?_, hi⟩
    have hlt := ofNat_lt_word h.m_bound hk
    have htk : BitVec.ofNat 64 k < fs.targetSize := by
      rw [BitVec.lt_def, hkw]
      exact Nat.lt_of_lt_of_le hk (h.size_le hn)
    have hnext : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hkw, Flat.toNat_ofNat_of_lt
        (show k + 1 < 2 ^ 64 by have hN : MAX_N = 1024 := rfl; omega)]
      simp only [BitVec.toNat_ofNat]
      have hN : MAX_N = 1024 := rfl
      omega
    rw [Flat.scan, dite_eq_left hlt]
    simp only [hn _ hlt, htk, not_true_eq_false, ↓reduceIte,
      BitVec.ofNat_eq_ofNat, hnext]
    exact he

theorem lowOk_of_map {planned : Vector Word MAX_N} {fs : Flat.St}
    (h : MapInv fs.size fs.targetSize ⟨fs.dest, fs.pos⟩)
    (hn : HasNoSurplus fs) (hp : PlannedSupport planned fs) : Flat.LowOk planned fs := by
  have hw : ∀ p, p < fs.size.toNat → (BitVec.ofNat 64 p).toNat = p :=
    fun p hi => Flat.toNat_ofNat_small (Nat.lt_of_lt_of_le hi h.m_bound)
  have hd : ∀ p, p < (lowShape fs).len → ∀ q, q < (lowShape fs).len →
      (lowShape fs).dest p = (lowShape fs).dest q → p = q := by
    intro p hpp q hqq he
    rw [lowShape_len] at hpp hqq
    rw [lowShape_dest fs hpp, lowShape_dest fs hqq] at he
    have hpe := ofNat_lt_word h.m_bound hpp
    have hqe := ofNat_lt_word h.m_bound hqq
    have hi := h.dest_inj hpe hqe (hn _ hpe) (BitVec.eq_of_toNat_eq he)
    have hiN := congrArg BitVec.toNat hi
    rwa [hw p hpp, hw q hqq] at hiN
  have hb : ∀ q, q < (lowShape fs).len →
      Bbu.isHole (lowPlan planned) ((lowShape fs).dest q) = false := by
    intro q hq
    rw [lowShape_len] at hq
    have hqe := ofNat_lt_word h.m_bound hq
    have hne := hn _ hqe
    have hdest := (h.dest _ hqe).resolve_left hne
    have hsupport := hp _ hqe hne
    have hplan := lowPlanR planned h.n_bound (get fs.dest (.ofNat 64 q))
      (BitVec.lt_def.mp hdest)
    rw [lowShape_dest fs hq]
    cases he : Bbu.isHole (lowPlan planned) (get fs.dest (.ofNat 64 q)).toNat
    · rfl
    · have he' : ((lowPlan planned)[(get fs.dest (.ofNat 64 q)).toNat]?).join = none :=
        Option.isNone_iff_eq_none.mp he
      exact False.elim (hsupport (hplan.mpr he'))
  intro l sc hscan hc
  obtain ⟨sc', he, hi⟩ := low_scan_spec h hn fs.size.toNat 0 (Flat.Scan.init l)
    (Nat.zero_add _) (Flat.scanInv_init _ _ l)
  have hsc : sc' = sc := Option.some.inj (he.symm.trans hscan)
  subst sc'
  rw [← lowShape_len fs] at hi
  obtain ⟨hFs, hFp⟩ := Flat.fill_spec (by rw [lowShape_len]; exact h.m_bound) hi hc
  have hlen : ((List.range (lowShape fs).len).filter (Flat.lowPark (lowPlan planned) (lowShape fs))).length =
      ((List.range (lowShape fs).len).filter (Flat.lowHole (lowPlan planned) (lowShape fs))).length := by
    rw [← hi.pc, ← hi.hc, hc]
  obtain ⟨hlt, hinj⟩ := Flat.lowF_bij hd hb
    (fun p => (get (Flat.fill sc 0 sc.permutation) (.ofNat 64 p)).toNat) hlen hFs hFp
  refine ⟨fun i hii => ?_, fun i hii j hjj hij => ?_⟩
  · have hiiN := BitVec.lt_def.mp hii
    have hh := hlt i.toNat (by rw [lowShape_len]; exact hiiN)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, lowShape_len] at hh
    exact BitVec.lt_def.mpr hh
  · apply BitVec.eq_of_toNat_eq
    apply hinj i.toNat (by rw [lowShape_len]; exact BitVec.lt_def.mp hii)
      j.toNat (by rw [lowShape_len]; exact BitVec.lt_def.mp hjj)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq, hij]

end Bbu.Unit.PlannerRunU
