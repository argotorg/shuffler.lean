module

public import FlatShuffler.FlatLowest
import all FlatShuffler.FlatLowest
public import FlatShuffler.ModelLowest
import all FlatShuffler.ModelLowest
public import FlatShuffler.FlatList.Permute
import all FlatShuffler.FlatList.Permute
public import FlatShuffler.FlatList.PermList
import all FlatShuffler.FlatList.PermList
public import FlatShuffler.FlatList.Loop
import all FlatShuffler.FlatList.Loop
public import FlatShuffler.FlatList.Ctor
import all FlatShuffler.FlatList.Ctor

@[expose] public section

/-!
The flat `permuteAtLowestHeight` (`FlatLowest.lean`) against the list `FlatShuffler.lowest`
(`ModelLowest.lean`).

The flat model sets each entry of the permutation once, directly. The list model does the
`setValue` steps of PR31. If the direct values are a bijection (`LowOk`), the `setValue` steps give
the same values (`SInv`, `FlatList/PermList.lean`). `FlatLowestTest.lean` has a planned mapping for
which the direct values are not a bijection and the two models differ.

`PlanR n planned pl`: the flat array `planned` and the list `pl` have the same holes below `n`.
-/

namespace FlatShuffler.Flat

-- The flat planned `m_positionOf` array and the list planned `positionOf` have the same holes below
-- `n`.
def PlanR (n : Nat) (planned : Vector Word maxStackSize) (pl : List (Option Nat)) : Prop :=
  ∀ d : Word, d.toNat < n → (get planned d = NONE ↔ (pl[d.toNat]?).join = none)

/-! ## The first loop of the list model -/

section
variable (pl : List (Option Nat)) (st : FlatShuffler.St)

-- The first loop sets the value of the slot at `p`.
def lowSets (p : Nat) : Bool := !isParked st p || isHole pl p

-- The value that the first loop sets for the slot at `p`.
def lowVal (p : Nat) : Nat := if isParked st p then p else st.dest p

-- `p` is a free hole.
def lowHole (p : Nat) : Bool := !isParked st p && isHole pl p

-- The slot at `p` is parked.
def lowPark (p : Nat) : Bool := isParked st p && !isHole pl p
end

theorem filter_range_succ (f : Nat → Bool) (k : Nat) :
    (List.range (k + 1)).filter f = (List.range k).filter f ++ if f k then [k] else [] := by
  rw [List.range_succ, List.filter_append]
  cases h : f k <;> simp [h]

-- The first loop of `FlatShuffler.lowestPerm` up to `k`: the `setValue` steps of the slots of `lowSets`,
-- the free holes and the parked slots.
theorem lowestScan_eq {n : Nat} (pl : List (Option Nat)) (st : FlatShuffler.St) (q0 : List Nat) :
    ∀ k, k ≤ n → (List.range k).foldlM (lowestStep n pl st) ⟨q0, [], []⟩ =
      .ok ⟨((List.range k).filter (lowSets pl st)).foldl
          (fun q p => setValue q p (lowVal st p)) q0,
        (List.range k).filter (lowHole pl st), (List.range k).filter (lowPark pl st)⟩
  | 0, _ => rfl
  | k + 1, hk => by
    rw [List.range_succ, List.foldlM_append, lowestScan_eq pl st q0 k (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, List.filter_append, List.foldl_append]
    unfold lowestStep
    have hk' : ¬n ≤ k := by omega
    cases hp : isParked st k <;> cases hh : isHole pl k <;>
      simp [hk', hp, hh, lowSets, lowVal, lowHole, lowPark] <;> rfl

/-! ## The first loop of the flat model -/

theorem ofNat_eq_iff {i : Nat} {w : Word} (hi : i < maxStackSize) : BitVec.ofNat 64 i = w ↔ i = w.toNat :=
  ⟨fun h => by rw [← h, toNat_ofNat_small hi],
    fun h => eq_of_toNat (by rw [toNat_ofNat_small hi, h])⟩

theorem length_filter_range_le (f : Nat → Bool) (k : Nat) : ((List.range k).filter f).length ≤ k :=
  Nat.le_trans (List.length_filter_le f _) (by simp)

-- The entries below `c` of `v` hold `L`. After `v[c] = x` and `c + 1`, they hold `L ++ [x]`.
theorem push_spec {v : Vector Word maxStackSize} {c : Word} {L : List Nat} {x : Nat}
    (hc : c.toNat = L.length) (hL : L.length < maxStackSize) (hx : x < maxStackSize)
    (h : ∀ i < c.toNat, (get v (.ofNat 64 i)).toNat = L[i]!) :
    (c + 1).toNat = (L ++ [x]).length ∧
      ∀ i < (c + 1).toNat, (get (put v c (.ofNat 64 x)) (.ofNat 64 i)).toNat = (L ++ [x])[i]! := by
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [MAX_N_eq] at hL; bv_omega
  refine ⟨by rw [hc1, hc, List.length_append, List.length_singleton], fun i hi => ?_⟩
  rw [hc1] at hi
  rw [get_put _ _ _ (by omega)]
  by_cases he : i = c.toNat
  · rw [ite_eq_left ((ofNat_eq_iff (by omega)).2 he), toNat_ofNat_small hx, he, hc]
    simp
  · rw [ite_eq_right (fun h' => he ((ofNat_eq_iff (by omega)).1 h')), h i (by omega),
      getElem!_append_left (by omega)]

-- The entries below `c'` of `v'` hold `L`, and `L` grows by `k` if `b`.
theorem grow_spec {v v' : Vector Word maxStackSize} {c c' : Word} {L : List Nat} {k : Nat} (b : Bool)
    (hc : c.toNat = L.length) (hL : L.length ≤ k) (hk : k < maxStackSize)
    (h : ∀ i < c.toNat, (get v (.ofNat 64 i)).toNat = L[i]!)
    (he : if b then v' = put v c (.ofNat 64 k) ∧ c' = c + 1 else v' = v ∧ c' = c) :
    c'.toNat = (L ++ if b then [k] else []).length ∧
      ∀ i < c'.toNat, (get v' (.ofNat 64 i)).toNat = (L ++ if b then [k] else [])[i]! := by
  cases b
  · obtain ⟨rfl, rfl⟩ := he
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ⟨hc, h⟩
  · obtain ⟨rfl, rfl⟩ := he
    exact push_spec hc (by omega) hk h

-- The permutation after the slot at `k`: `v[k] = w` if the slot gets a value.
theorem perm_spec {v v' : Vector Word maxStackSize} {f : Nat → Bool} {g : Nat → Nat} {k : Nat}
    (hk : k < maxStackSize) (h : ∀ p < k, f p = true → (get v (.ofNat 64 p)).toNat = g p)
    (he : if f k then ∃ w : Word, w.toNat = g k ∧ v' = put v (.ofNat 64 k) w else v' = v) :
    ∀ p < k + 1, f p = true → (get v' (.ofNat 64 p)).toNat = g p := by
  intro p hp hf
  have hpk : p < maxStackSize := by omega
  by_cases hpe : p = k
  · subst hpe
    rw [ite_eq_left hf] at he
    obtain ⟨w, hw, rfl⟩ := he
    rw [get_put_self _ _ (by rw [toNat_ofNat_small hk]; exact hk), hw]
  · have hne : BitVec.ofNat 64 p ≠ BitVec.ofNat 64 k := fun h' =>
      hpe (by rw [← toNat_ofNat_small hpk, h', toNat_ofNat_small hk])
    have hv : get v' (.ofNat 64 p) = get v (.ofNat 64 p) := by
      split at he
      · obtain ⟨w, _, rfl⟩ := he; exact get_put_ne _ _ hne
      · rw [he]
    rw [hv]; exact h p (by omega) hf

-- The locals of the first loop of the flat model up to `k` hold the lists of the list model
-- (`lowestScan_eq`).
structure ScanInv (pl : List (Option Nat)) (st : FlatShuffler.St) (k : Nat) (sc : Scan) : Prop where
  hc : sc.holeCount.toNat = ((List.range k).filter (lowHole pl st)).length
  pc : sc.parkedCount.toNat = ((List.range k).filter (lowPark pl st)).length
  holes : ∀ i < sc.holeCount.toNat,
    (get sc.holes (.ofNat 64 i)).toNat = ((List.range k).filter (lowHole pl st))[i]!
  parked : ∀ i < sc.parkedCount.toNat,
    (get sc.parked (.ofNat 64 i)).toNat = ((List.range k).filter (lowPark pl st))[i]!
  perm : ∀ p < k, lowSets pl st p = true →
    (get sc.permutation (.ofNat 64 p)).toNat = lowVal st p

theorem scanInv_init (pl : List (Option Nat)) (st : FlatShuffler.St) (l : Locals) :
    ScanInv pl st 0 (Scan.init l) :=
  ⟨by simp [Scan.init], by simp [Scan.init], fun _ h => absurd h (by simp [Scan.init]),
    fun _ h => absurd h (by simp [Scan.init]), fun _ h => absurd h (by omega)⟩

-- `ScanInv` at `k + 1` from the changes of the locals at `k`.
theorem ScanInv.next {pl : List (Option Nat)} {st : FlatShuffler.St} {k : Nat} {sc sc' : Scan}
    (hk : k < maxStackSize) (h : ScanInv pl st k sc)
    (e1 : if lowHole pl st k then
        sc'.holes = put sc.holes sc.holeCount (.ofNat 64 k) ∧ sc'.holeCount = sc.holeCount + 1
      else sc'.holes = sc.holes ∧ sc'.holeCount = sc.holeCount)
    (e2 : if lowPark pl st k then
        sc'.parked = put sc.parked sc.parkedCount (.ofNat 64 k) ∧
          sc'.parkedCount = sc.parkedCount + 1
      else sc'.parked = sc.parked ∧ sc'.parkedCount = sc.parkedCount)
    (e3 : if lowSets pl st k then
        ∃ w : Word, w.toNat = lowVal st k ∧ sc'.permutation = put sc.permutation (.ofNat 64 k) w
      else sc'.permutation = sc.permutation) :
    ScanInv pl st (k + 1) sc' := by
  have g1 := grow_spec _ h.hc (length_filter_range_le _ k) hk h.holes e1
  have g2 := grow_spec _ h.pc (length_filter_range_le _ k) hk h.parked e2
  rw [← filter_range_succ] at g1 g2
  exact ⟨g1.1, g2.1, g1.2, g2.2, perm_spec hk h.perm e3⟩

theorem scanInv_step {e : Env} {fs : St} {st : FlatShuffler.St} {planned : Vector Word maxStackSize}
    {pl : List (Option Nat)} (hs : Sim e fs st) (hpl : PlanR fs.targetSize.toNat planned pl)
    {k : Nat} (hk : k < st.len) {sc : Scan} (h : ScanInv pl st k sc) :
    ScanInv pl st (k + 1) (scanStep planned fs (.ofNat 64 k) (get fs.dest (.ofNat 64 k)) sc) := by
  have hN := hs.len_lt
  have hkN : k < maxStackSize := by omega
  have hkw := toNat_ofNat_small hkN
  have hdk := hs.dest (.ofNat 64 k) (by rw [hkw]; exact hk)
  rw [hkw] at hdk
  have hH : (get planned (.ofNat 64 k) == NONE) = isHole pl k := by
    have := hpl (.ofNat 64 k) (by rw [hkw]; have := hs.len_le; omega)
    rw [hkw] at this
    unfold isHole
    rw [Bool.eq_iff_iff, beq_iff_eq, Option.isNone_iff_eq_none]
    exact this
  have hP : decide (fs.size ≤ get fs.dest (.ofNat 64 k)) = isParked st k := by
    unfold isParked
    rw [← hdk, ← hs.size]
    exact decide_eq_decide.2 BitVec.le_def
  apply ScanInv.next hkN h <;> simp only [scanStep, lowHole, lowPark, lowSets, lowVal, hH, hP] <;>
    cases b1 : isParked st k <;> cases b2 : isHole pl k <;>
    simp
  all_goals first | exact ⟨_, hdk, rfl⟩ | exact ⟨_, hkw, rfl⟩

theorem scan_spec {e : Env} {fs : St} {st : FlatShuffler.St} {planned : Vector Word maxStackSize}
    {pl : List (Option Nat)} (hs : Sim e fs st) (hpl : PlanR fs.targetSize.toNat planned pl) :
    ∀ d k sc, k + d = st.len → ScanInv pl st k sc →
      ∃ sc', scan planned fs (.ofNat 64 k) sc = some sc' ∧ ScanInv pl st st.len sc'
  | 0, k, sc, hd, h => by
    have hN := hs.len_lt
    have hsz := hs.size
    refine ⟨sc, ?_, by rw [← hd]; exact h⟩
    rw [scan, dite_eq_right]
    intro hlt
    rw [BitVec.lt_def, toNat_ofNat_of_lt (show k < 2 ^ 64 by rw [MAX_N_eq] at hN; omega)] at hlt
    omega
  | d + 1, k, sc, hd, h => by
    have hk : k < st.len := by omega
    have hN := hs.len_lt
    have hkN : k < maxStackSize := by omega
    obtain ⟨sc', h1, h2⟩ := scan_spec hs hpl d (k + 1) _ (by omega) (scanInv_step hs hpl hk h)
    refine ⟨sc', ?_, h2⟩
    have hkw := toNat_ofNat_small hkN
    have hlt : BitVec.ofNat 64 k < fs.size := by rw [BitVec.lt_def, hkw, hs.size]; exact hk
    have hdk := hs.dest (.ofNat 64 k) (by rw [hkw]; exact hk)
    have hdn := hs.dest_lt hk
    have hn := hs.n
    have hnN := hs.n_le
    have hle := hs.len_le
    have hne : get fs.dest (.ofNat 64 k) ≠ NONE :=
      ne_NONE (by rw [hdk, hkw]; rw [MAX_N_eq] at hnN; omega)
    have htk : BitVec.ofNat 64 k < fs.targetSize := by rw [BitVec.lt_def, hkw]; omega
    have hk1 : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
      apply eq_of_toNat
      rw [BitVec.toNat_add, hkw, toNat_ofNat_of_lt (show k + 1 < 2 ^ 64 by rw [MAX_N_eq] at hkN; omega)]
      rw [MAX_N_eq] at hkN
      simp
      omega
    rw [scan, dite_eq_left hlt]
    simp only [hne, htk, ite_false, not_true_eq_false, hk1]
    exact h1

/-! ## The second loop of the flat model -/

-- `fill` from `j` keeps the entry at `q` if no parked slot from `j` on is `q`.
theorem fill_other (sc : Scan) (q j : Word) (v : Vector Word maxStackSize)
    (h : ∀ i : Word, j ≤ i → i < sc.parkedCount → get sc.parked i ≠ q) :
    get (fill sc j v) q = get v q := by
  rw [fill]
  split
  · rename_i hj
    rw [fill_other sc q (j + 1) _ (fun i h1 h2 => h i (by bv_omega) h2),
      get_put_ne _ _ (Ne.symm (h j (BitVec.le_refl _) hj))]
  · rfl
termination_by (sc.parkedCount - j).toNat
decreasing_by bv_omega

-- `fill` from `j` sets the entry of the parked slot `i ≥ j` to the hole `i`, if the parked slots
-- are distinct.
theorem fill_parked (sc : Scan)
    (hd : ∀ a b : Word, a < sc.parkedCount → b < sc.parkedCount →
      get sc.parked a = get sc.parked b → a = b)
    (i : Word) (hi : i < sc.parkedCount) (hiN : (get sc.parked i).toNat < maxStackSize)
    (j : Word) (v : Vector Word maxStackSize) (hj : j ≤ i) :
    get (fill sc j v) (get sc.parked i) = get sc.holes i := by
  rw [fill, dite_eq_left (show j < sc.parkedCount by bv_omega)]
  by_cases he : j = i
  · subst he
    rw [fill_other sc _ _ _ (fun a h1 h2 h3 => by have := hd a j h2 hi h3; bv_omega),
      get_put_self _ _ hiN]
  · exact fill_parked sc hd i hi hiN (j + 1) _ (by bv_omega)
termination_by (sc.parkedCount - j).toNat
decreasing_by
  have h1 : j.toNat < i.toNat := by have := BitVec.le_def.1 hj; have := toNat_ne_of_ne he; omega
  have h2 := BitVec.lt_def.1 hi
  bv_omega

/-! ## The second loop against the lists -/

theorem getElem!_inj_of_lt {L : List Nat} (h : L.Pairwise (· < ·)) {i j : Nat} (hi : i < L.length)
    (hj : j < L.length) (he : L[i]! = L[j]!) : i = j := by
  rw [getElem!_pos L i hi, getElem!_pos L j hj] at he
  rw [List.pairwise_iff_getElem] at h
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · have := h i j hi hj h1; omega
  · exact h1
  · have := h j i hj hi h1; omega

theorem lowSets_eq (pl : List (Option Nat)) (st : FlatShuffler.St) (p : Nat) :
    lowSets pl st p = !lowPark pl st p := by
  unfold lowSets lowPark
  cases isParked st p <;> cases isHole pl p <;> rfl

theorem lowVal_lt {st : FlatShuffler.St} {p : Nat} (hp : p < st.len) : lowVal st p < st.len := by
  unfold lowVal
  split
  · exact hp
  · rename_i h'; unfold isParked at h'; simp at h'; exact h'

theorem ofNat_toNat (i : Word) : BitVec.ofNat 64 i.toNat = i := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

-- The permutation after the second loop: the value of the first loop at a slot of `lowSets`, and
-- the `i`-th free hole at the `i`-th parked slot.
theorem fill_spec {pl : List (Option Nat)} {st : FlatShuffler.St} {sc : Scan} (hN : st.len ≤ maxStackSize)
    (hinv : ScanInv pl st st.len sc) (hc : sc.parkedCount = sc.holeCount) :
    (∀ p < st.len, lowSets pl st p = true →
      (get (fill sc 0 sc.permutation) (.ofNat 64 p)).toNat = lowVal st p) ∧
    ∀ i < ((List.range st.len).filter (lowHole pl st)).length,
      (get (fill sc 0 sc.permutation)
        (.ofNat 64 ((List.range st.len).filter (lowPark pl st))[i]!)).toNat =
        ((List.range st.len).filter (lowHole pl st))[i]! := by
  have hpc := hinv.pc
  have hhc := hinv.hc
  have hpk0 := hinv.parked
  have hhk0 := hinv.holes
  have hperm := hinv.perm
  have hPl := length_filter_range_le (lowPark pl st) st.len
  have hHl := length_filter_range_le (lowHole pl st) st.len
  have hPs : ((List.range st.len).filter (lowPark pl st)).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hPm : ∀ x ∈ (List.range st.len).filter (lowPark pl st), x < st.len ∧ lowPark pl st x = true :=
    fun x h => by rw [List.mem_filter, List.mem_range] at h; exact h
  generalize (List.range st.len).filter (lowPark pl st) = P at hpc hpk0 hPl hPs hPm ⊢
  generalize (List.range st.len).filter (lowHole pl st) = H at hhc hhk0 hHl ⊢
  have hPH : P.length = H.length := by rw [← hpc, ← hhc, hc]
  have hPi : ∀ i < P.length, P[i]! < st.len ∧ lowPark pl st P[i]! = true := fun i h =>
    hPm _ (by rw [getElem!_pos P i h]; exact List.getElem_mem h)
  have hw : ∀ p < st.len, (BitVec.ofNat 64 p).toNat = p := fun p h => toNat_ofNat_small (by omega)
  have hpk : ∀ i : Word, i < sc.parkedCount → (get sc.parked i).toNat = P[i.toNat]! := fun i h => by
    have := hpk0 i.toNat (BitVec.lt_def.1 h)
    rw [ofNat_toNat] at this
    exact this
  have hhk : ∀ i : Word, i < sc.holeCount → (get sc.holes i).toNat = H[i.toNat]! := fun i h => by
    have := hhk0 i.toNat (BitVec.lt_def.1 h)
    rw [ofNat_toNat] at this
    exact this
  refine ⟨fun p hp hs' => ?_, fun i hi => ?_⟩
  · rw [fill_other sc _ _ _ (fun i _ h2 he => ?_)]
    · exact hperm p hp hs'
    · have h3 := hpk i h2
      rw [he, hw p hp] at h3
      have h4 := (hPi i.toNat (by rw [← hpc]; exact BitVec.lt_def.1 h2)).2
      rw [← h3, lowSets_eq] at *
      rw [h4] at hs'
      exact Bool.false_ne_true hs'
  · have hiw : (BitVec.ofNat 64 i).toNat = i := toNat_ofNat_small (by omega)
    have hic : BitVec.ofNat 64 i < sc.parkedCount := by
      rw [BitVec.lt_def, hiw, hpc]; omega
    have h1 := hpk _ hic
    rw [hiw] at h1
    have hPin := (hPi i (by omega)).1
    have h2 : get sc.parked (.ofNat 64 i) = .ofNat 64 P[i]! :=
      ((ofNat_eq_iff (by omega)).2 h1.symm).symm
    rw [← h2, fill_parked sc ?_ _ hic (by rw [h1]; omega) 0 _ (by bv_omega),
      hhk _ (hc ▸ hic), hiw]
    intro a b ha hb' he
    have := hpk a ha
    rw [he, hpk b hb'] at this
    have hal := BitVec.lt_def.1 ha
    have hbl := BitVec.lt_def.1 hb'
    rw [hpc] at hal hbl
    exact eq_of_toNat (getElem!_inj_of_lt hPs hbl hal this).symm

/-! ## The values of the second loop are a bijection -/

section
variable {pl : List (Option Nat)} {st : FlatShuffler.St}
  (hdist : ∀ p < st.len, ∀ q < st.len, st.dest p = st.dest q → p = q)
  (hbound : ∀ q < st.len, isHole pl (st.dest q) = false)
include hdist hbound

theorem lowVal_inj {p q : Nat} (hp : p < st.len) (hq : q < st.len)
    (hsp : lowSets pl st p = true) (hsq : lowSets pl st q = true)
    (h : lowVal st p = lowVal st q) : p = q := by
  unfold lowSets at hsp hsq
  unfold lowVal at h
  cases bp : isParked st p <;> cases bq : isParked st q <;> simp [bp, bq] at h hsp hsq
  · exact hdist p hp q hq h
  · rw [← h, hbound p hp] at hsq; exact absurd hsq Bool.false_ne_true
  · rw [h, hbound q hq] at hsp; exact absurd hsp Bool.false_ne_true
  · exact h

omit hdist in
theorem lowHole_ne {h q : Nat} (hh : lowHole pl st h = true) (hq : q < st.len) :
    lowVal st q ≠ h := by
  unfold lowHole at hh
  unfold lowVal
  intro he
  cases bq : isParked st q <;> simp [bq] at he
  · rw [← he, hbound q hq] at hh; simp at hh
  · subst he; simp [bq] at hh

-- A map with the values of `fill_spec` is a bijection of the offsets below the length.
theorem lowF_bij (F : Nat → Nat)
    (hlen : ((List.range st.len).filter (lowPark pl st)).length =
      ((List.range st.len).filter (lowHole pl st)).length)
    (hFs : ∀ p < st.len, lowSets pl st p = true → F p = lowVal st p)
    (hFp : ∀ i < ((List.range st.len).filter (lowHole pl st)).length,
      F ((List.range st.len).filter (lowPark pl st))[i]! =
        ((List.range st.len).filter (lowHole pl st))[i]!) :
    (∀ p < st.len, F p < st.len) ∧ ∀ p < st.len, ∀ q < st.len, F p = F q → p = q := by
  have hcase : ∀ p < st.len, lowSets pl st p = true ∨
      ∃ i < ((List.range st.len).filter (lowPark pl st)).length,
        ((List.range st.len).filter (lowPark pl st))[i]! = p := by
    intro p hp
    cases hk : lowPark pl st p
    · left; rw [lowSets_eq, hk]; rfl
    · right
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (List.mem_filter.2 ⟨List.mem_range.2 hp, hk⟩)
      exact ⟨i, hi, by rw [getElem!_pos _ i hi]; exact he⟩
  have hHm : ∀ x ∈ (List.range st.len).filter (lowHole pl st), x < st.len ∧ lowHole pl st x = true :=
    fun x h => by rw [List.mem_filter, List.mem_range] at h; exact h
  have hHs : ((List.range st.len).filter (lowHole pl st)).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  generalize (List.range st.len).filter (lowPark pl st) = P at hcase hlen hFp
  generalize (List.range st.len).filter (lowHole pl st) = H at hHm hHs hlen hFp
  have hHi : ∀ i < H.length, H[i]! < st.len ∧ lowHole pl st H[i]! = true := fun i h =>
    hHm _ (by rw [getElem!_pos H i h]; exact List.getElem_mem h)
  refine ⟨fun p hp => ?_, fun p hp q hq he => ?_⟩
  · rcases hcase p hp with hs | ⟨i, hi, rfl⟩
    · rw [hFs p hp hs]; exact lowVal_lt hp
    · rw [hFp i (by omega)]; exact (hHi i (by omega)).1
  · rcases hcase p hp with hsp | ⟨i, hi, rfl⟩ <;> rcases hcase q hq with hsq | ⟨j, hj, rfl⟩
    · rw [hFs p hp hsp, hFs q hq hsq] at he
      exact lowVal_inj hdist hbound hp hq hsp hsq he
    · rw [hFs p hp hsp, hFp j (by omega)] at he
      exact absurd he (lowHole_ne hbound (hHi j (by omega)).2 hp)
    · rw [hFp i (by omega), hFs q hq hsq] at he
      exact absurd he.symm (lowHole_ne hbound (hHi i (by omega)).2 hq)
    · rw [hFp i (by omega), hFp j (by omega)] at he
      rw [getElem!_inj_of_lt hHs (by omega) (by omega) he]

-- If the destinations are distinct and each target offset of a slot is not a hole, `LowOk` holds.
theorem lowOk_of {e : Env} {fs : St} {planned : Vector Word maxStackSize} (hs : Sim e fs st)
    (hpl : PlanR fs.targetSize.toNat planned pl) : LowOk planned fs := by
  intro l sc hscan hc
  have hN := hs.len_lt
  have hsz := hs.size
  obtain ⟨sc', hscan', hinv⟩ :=
    scan_spec hs hpl st.len 0 (Scan.init l) (by omega) (scanInv_init pl st l)
  have hsc : sc' = sc :=
    Option.some.inj ((show scan planned fs 0 (Scan.init l) = some sc' from hscan').symm.trans hscan)
  subst hsc
  obtain ⟨hFs, hFp⟩ := fill_spec hN hinv hc
  have hlen : ((List.range st.len).filter (lowPark pl st)).length =
      ((List.range st.len).filter (lowHole pl st)).length := by
    rw [← hinv.pc, ← hinv.hc, hc]
  obtain ⟨hlt, hinj⟩ := lowF_bij hdist hbound
    (fun p => (get (fill sc' 0 sc'.permutation) (.ofNat 64 p)).toNat) hlen hFs hFp
  have hlt' : ∀ i : Word, i < fs.size → i.toNat < st.len := fun i h => by
    rw [← hsz]; exact BitVec.lt_def.1 h
  refine ⟨fun i hi => ?_, fun i hi k hk he => ?_⟩
  · have := hlt i.toNat (hlt' i hi)
    rw [ofNat_toNat] at this
    rw [BitVec.lt_def, hsz]; exact this
  · refine eq_of_toNat (hinj i.toNat (hlt' i hi) k.toNat (hlt' k hk) ?_)
    rw [ofNat_toNat, ofNat_toNat, he]
end

/-! ## The two models -/

theorem sinv_range (n : Nat) : SInv n (fun _ => True) (· < n) (List.range n) := by
  refine SInv.of_isPerm (by simp) ⟨fun i h => ?_, fun i hi j hj h => ?_⟩
    (fun d hd => ⟨d, trivial, hd, ?_⟩)
  · rw [List.getElem_range]; exact h
  · rw [List.getElem_range, List.getElem_range] at h; exact h
  · rw [getElem!_pos _ _ (by simp; exact hd), List.getElem_range]

theorem sim_lowest {e : Env} {fs : St} {st : FlatShuffler.St} {planned : Vector Word maxStackSize}
    {pl : List (Option Nat)} (hs : Sim e fs st) (hpl : PlanR fs.targetSize.toNat planned pl)
    (hb : LowOk planned fs) (l : Locals) :
    SimR e (permuteAtLowestHeight planned l fs) (FlatShuffler.lowest e.n pl st) := by
  have hN := hs.len_lt
  have hen := hs.n
  have hle := hs.len_le
  have hsz := hs.size
  obtain ⟨sc, hscan, hinv⟩ :=
    scan_spec hs hpl st.len 0 (Scan.init l) (by omega) (scanInv_init pl st l)
  have hscan0 : scan planned fs 0 (Scan.init l) = some sc := hscan
  have hlist := lowestScan_eq (n := e.n) pl st (List.range st.len) st.len (by omega)
  have bind_ok : ∀ {α β : Type} (a : α) (f : α → M β), (Except.ok a : M α).bind f = f a :=
    fun _ _ => rfl
  unfold permuteAtLowestHeight FlatShuffler.lowest FlatShuffler.lowestPerm
  rw [hscan0, hlist, bind_ok]
  dsimp only
  -- The lists of the list model and their properties.
  have hsort : ∀ f : Nat → Bool, ((List.range st.len).filter f).Pairwise (· < ·) :=
    fun f => List.pairwise_lt_range.filter f
  have hmem : ∀ (f : Nat → Bool) x, x ∈ (List.range st.len).filter f ↔ x < st.len ∧ f x = true :=
    fun f x => by rw [List.mem_filter, List.mem_range]
  have hPs : ((List.range st.len).filter (lowPark pl st)).mergeSort (fun a b => decide (a ≤ b)) =
      (List.range st.len).filter (lowPark pl st) :=
    List.mergeSort_of_pairwise ((hsort _).imp fun h => by simp; omega)
  rw [hPs]
  by_cases hc0 : sc.parkedCount ≠ sc.holeCount
  · have hne : ((List.range st.len).filter (lowPark pl st)).length ≠
        ((List.range st.len).filter (lowHole pl st)).length := by
      rw [← hinv.pc, ← hinv.hc]; exact fun h => hc0 (eq_of_toNat h)
    rw [ite_eq_left hc0, ite_eq_left hne]
    rfl
  have hc : sc.parkedCount = sc.holeCount := Decidable.of_not_not hc0
  have hne : ¬((List.range st.len).filter (lowPark pl st)).length ≠
      ((List.range st.len).filter (lowHole pl st)).length := by
    rw [← hinv.pc, ← hinv.hc, hc]; exact fun h => h rfl
  rw [ite_eq_right hc0, ite_eq_right hne, bind_ok]
  obtain ⟨hlt, hinj⟩ := hb l sc hscan0 hc
  obtain ⟨hFs0, hFp0⟩ := fill_spec hN hinv hc
  have hPl := length_filter_range_le (lowPark pl st) st.len
  have hHl := length_filter_range_le (lowHole pl st) st.len
  have hPs := hsort (lowPark pl st)
  have hPm : ∀ x ∈ (List.range st.len).filter (lowPark pl st), x < st.len ∧ lowPark pl st x = true :=
    fun x h => (hmem _ x).1 h
  generalize hv : fill sc 0 sc.permutation = v at hlt hinj hFs0 hFp0 ⊢
  generalize hP : (List.range st.len).filter (lowPark pl st) = P at hPl hPs hPm hne hFp0 ⊢
  generalize hH : (List.range st.len).filter (lowHole pl st) = H at hHl hne hFp0 ⊢
  have hPH : P.length = H.length := by omega
  have hPi : ∀ i < P.length, P[i]! < st.len ∧ lowPark pl st P[i]! = true := fun i h =>
    hPm _ (by rw [getElem!_pos P i h]; exact List.getElem_mem h)
  -- The flat permutation at each offset: `F`.
  let F : Nat → Nat := fun p => (get v (.ofNat 64 p)).toNat
  have hw : ∀ p < st.len, (BitVec.ofNat 64 p).toNat = p := fun p h => toNat_ofNat_small (by omega)
  have hF : ∀ p < st.len, F p < st.len := fun p h => by
    have := hlt (.ofNat 64 p) (by rw [BitVec.lt_def, hw p h, hsz]; exact h)
    rw [BitVec.lt_def, hsz] at this
    exact this
  have hFi : ∀ p < st.len, ∀ q < st.len, F p = F q → p = q := fun p hp q hq h => by
    have := hinj (.ofNat 64 p) (by rw [BitVec.lt_def, hw p hp, hsz]; exact hp) (.ofNat 64 q)
      (by rw [BitVec.lt_def, hw q hq, hsz]; exact hq) (eq_of_toNat h)
    rw [← hw p hp, ← hw q hq, this]
  have hFs : ∀ p < st.len, lowSets pl st p = true → F p = lowVal st p := hFs0
  have hFp : ∀ i < H.length, H[i]! = F P[i]! := fun i hi => (hFp0 i hi).symm
  -- The first loop of the list model.
  have hSi : ∀ x ∈ (List.range st.len).filter (lowSets pl st), x < st.len ∧ lowSets pl st x = true :=
    fun x h => (hmem _ x).1 h
  obtain ⟨s1, s1m, -⟩ := SInv.foldl (fun x => x) (lowVal st) _ _ (sinv_range st.len)
    (List.nodup_range.filter _) (fun x h => ⟨trivial, (hSi x h).1, lowVal_lt (hSi x h).1⟩)
    (fun _ _ _ _ h => h)
    (fun x hx y hy h => by
      have hx' := hSi x hx
      have hy' := hSi y hy
      exact hFi x hx'.1 y hy'.1 (by rw [hFs x hx'.1 hx'.2, hFs y hy'.1 hy'.2]; exact h))
  generalize hq1 : List.foldl (fun q p => setValue q p (lowVal st p)) (List.range st.len)
    ((List.range st.len).filter (lowSets pl st)) = q1 at s1 s1m ⊢
  have hq1F : ∀ p < st.len, lowSets pl st p = true → q1[p]! = F p := fun p hp h => by
    rw [hFs p hp h]; exact s1m p ((hmem _ p).2 ⟨hp, h⟩)
  -- The second loop of the list model.
  have hPinj : ∀ x ∈ List.range H.length, ∀ y ∈ List.range H.length, P[x]! = P[y]! → x = y :=
    fun x hx y hy h => getElem!_inj_of_lt hPs (by simp at hx; omega) (by simp at hy; omega) h
  obtain ⟨s2, s2m, s2o⟩ := SInv.foldl (fun i => P[i]!) (fun i => H[i]!) (List.range H.length) q1 s1
    List.nodup_range
    (fun x h => by
      simp only [List.mem_range] at h
      exact ⟨trivial, (hPi x (by omega)).1, by rw [hFp x h]; exact hF _ (hPi x (by omega)).1⟩)
    hPinj
    (fun x hx y hy h => by
      simp only [List.mem_range] at hx hy
      rw [hFp x hx, hFp y hy] at h
      exact hPinj x (by simpa using hx) y (by simpa using hy)
        (hFi _ (hPi x (by omega)).1 _ (hPi y (by omega)).1 h))
  generalize hq2 : List.foldl (fun q x => setValue q P[x]! H[x]!) q1 (List.range H.length) = q2
    at s2 s2m s2o ⊢
  have hq2F : ∀ p < st.len, q2[p]! = F p := fun p hp => by
    cases hk : lowPark pl st p
    · have hs' : lowSets pl st p = true := by rw [lowSets_eq, hk]; rfl
      rw [s2o p (fun x hx => ?_), hq1F p hp hs']
      simp only [List.mem_range] at hx
      have hx' := hPi x (by omega)
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [h, hk] at hx'; exact Bool.false_ne_true hx'.2
      · rw [hq1F p hp hs', hFp x hx] at h
        have := hFi _ hx'.1 _ hp h
        rw [this, hk] at hx'; exact Bool.false_ne_true hx'.2
    · have hm : p ∈ P := hP ▸ (hmem _ p).2 ⟨hp, hk⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
      have h := s2m i (List.mem_range.2 (by omega))
      have h2 := hFp i (by omega)
      rw [getElem!_pos P i hi] at h h2
      rw [h, h2]
  have hpv : PermV st.len v q2 := ⟨s2.len, fun i hi => by
    rw [hq2F i.toNat hi]; show _ = (get v (.ofNat 64 i.toNat)).toNat; rw [ofNat_toNat]⟩
  exact sim_permute hs hpv s2.isPerm

/-! ## The entry -/

theorem put_NONE {α : Type} (v : Vector α maxStackSize) (x : α) : put v NONE x = v := by
  unfold put
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_setIfInBounds_ne]
  have : NONE.toNat = 2 ^ 64 - 1 := rfl
  rw [this]; rw [MAX_N_eq] at hi; omega

-- A loop maps a projection `g` with the step `f'`.
theorem foldl_proj {α β γ : Type} (g : α → γ) {f : α → β → α} {f' : γ → β → γ}
    (hf : ∀ a b, g (f a b) = f' (g a) b) (l : List β) (a : α) :
    g (l.foldl f a) = l.foldl f' (g a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => rw [List.foldl_cons, List.foldl_cons, ih, hf]

-- The planned positions of the entry are the positions of the first two loops of the
-- constructor.
theorem plannedPos_eq (m n : Word) (dests up : Vector Word maxStackSize) (s0 : St) (h0 : s0.pos = up) :
    plannedPos m n dests up =
      ((ofs m.toNat).foldl (bindF dests) ((ofs n.toNat).foldl clearF s0)).pos := by
  rw [foldl_proj St.pos (f' := fun p q => if get dests q = NONE then p else put p (get dests q) q)
      (fun a b => ?_),
    foldl_proj St.pos (f' := fun p d => put p d NONE) (fun _ _ => rfl), h0]
  · rfl
  · show put a.pos (get dests b) b = _
    split
    · rename_i h; rw [h, put_NONE]
    · rfl

theorem planR_ctor {m n : Word} {dest : Vector Word maxStackSize} (up : Vector Word maxStackSize) (hm : m ≤ n)
    (hn : n.toNat ≤ maxStackSize) (hd : Dests n.toNat (listDests m.toNat dest)) :
    PlanR n.toNat (plannedPos m n dest up) (initPositionOf n.toNat (listDests m.toNat dest)) := by
  have hmn : m.toNat ≤ n.toNat := hm
  have hM : m.toNat ≤ maxStackSize := by omega
  let s0 : St := ctor0 (Vector.replicate maxStackSize default) 0 (Vector.replicate maxStackSize default) 0
    (fun _ => 0) ⟨up, up, 0, 0⟩
  rw [plannedPos_eq m n dest up s0 rfl]
  obtain ⟨-, hb2⟩ := bind_loop hn hmn hd _ (fun d h => clear_pos s0 hn h) (Nat.le_refl _)
  obtain ⟨-, h2⟩ := initPositionOf_prefix hd _ (Nat.le_refl _)
  intro d hd'
  rw [hb2 d hd']
  have hip : initPos n.toNat (listDests m.toNat dest) m.toNat =
      initPositionOf n.toNat (listDests m.toNat dest) := by
    rw [initPositionOf, listDests_length dest hM]; rfl
  rw [hip]
  cases hj : ((initPositionOf n.toNat (listDests m.toNat dest))[d.toNat]?).join with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some i =>
    obtain ⟨hi, -⟩ := (h2 d.toNat i).1 hj
    rw [listDests_length dest hM] at hi
    refine ⟨fun h => absurd h (ne_NONE ?_), fun h => nomatch h⟩
    show (BitVec.ofNat 64 i).toNat < _
    rw [toNat_ofNat_small (by omega)]
    rw [MAX_N_eq] at hM
    omega

-- The planned mapping of the entry is the mapping of the constructor: `LowOk` holds.
theorem lowOk_ctor {m n : Word} {data target : Vector StackSlot maxStackSize} {dest : Vector Word maxStackSize}
    {spilled : BitVec 32 → BitVec 8} (u : Uninit) (up : Vector Word maxStackSize) (hm : m ≤ n)
    (hn : n.toNat ≤ maxStackSize) (hd : Dests n.toNat (listDests m.toNat dest)) :
    LowOk (plannedPos m n dest up) (ctor data m target n dest spilled u) := by
  have hmn : m.toNat ≤ n.toNat := hm
  have hM : m.toNat ≤ maxStackSize := by omega
  have hs := sim_ctor (data := data) (target := target) (spilled := spilled) u hm hn hd
  have htn : (ctor data m target n dest spilled u).targetSize.toNat = n.toNat := by
    rw [← hs.n, listEnv_n target spilled hn]
  have hl : (listSource m.toNat data).length = (listDests m.toNat dest).length := by
    rw [listSource_length data hM, listDests_length dest hM]
  have hds : (init (listEnv n.toNat target spilled) (listSource m.toNat data)
      (listDests m.toNat dest)).dests = listDests m.toNat dest := map_dest_zipWith _ _ hl
  have hlen := init_len (e := listEnv n.toNat target spilled) hl
  generalize init (listEnv n.toNat target spilled) (listSource m.toNat data)
    (listDests m.toNat dest) = st at hs hds hlen
  have hdl : (listDests m.toNat dest).length = st.len := by rw [hlen, hl]
  have hdest : ∀ p, st.dest p = (listDests m.toNat dest)[p]! := fun p => by rw [St.dest_eq, hds]
  obtain ⟨-, h2⟩ := initPositionOf_prefix hd _ (Nat.le_refl _)
  refine lowOk_of (pl := initPositionOf n.toNat (listDests m.toNat dest))
    (fun p hp q hq h => ?_) (fun q hq => ?_) hs (by rw [htn]; exact planR_ctor up hm hn hd)
  · rw [hdest, hdest, getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)] at h
    exact hd.2 p (by omega) q (by omega) h
  · have h3 := (h2 (st.dest q) q).2 ⟨by omega, by rw [hdest, getElem!_pos _ _ (by omega)]⟩
    unfold isHole initPositionOf
    rw [h3]
    rfl

theorem permute_at_lowest_height_rel {m n : Word} {data target : Vector StackSlot maxStackSize}
    {dest : Vector Word maxStackSize} {spilled : BitVec 32 → BitVec 8} (u : Uninit)
    (up : Vector Word maxStackSize) (l : Locals) (hm : m ≤ n) (hn : n.toNat ≤ maxStackSize)
    (hd : Dests n.toNat (listDests m.toNat dest)) :
    Rel (permute_at_lowest_height m n data target dest spilled u up l)
      (FlatShuffler.lowest n.toNat (initPositionOf n.toNat (listDests m.toNat dest))
        (FlatShuffler.init (listEnv n.toNat target spilled) (listSource m.toNat data)
          (listDests m.toNat dest))) := by
  have hg : ¬(m > BitVec.ofNat 64 maxStackSize ∨ n > BitVec.ofNat 64 maxStackSize) := by
    have hmn : m.toNat ≤ n.toNat := hm
    rw [MAX_N_eq] at hn ⊢
    intro h
    rcases h with h | h <;> bv_omega
  have hs := sim_ctor (data := data) (target := target) (spilled := spilled) u hm hn hd
  have htn : (ctor data m target n dest spilled u).targetSize.toNat = n.toNat := by
    rw [← hs.n, listEnv_n target spilled hn]
  have hp : PlanR (ctor data m target n dest spilled u).targetSize.toNat (plannedPos m n dest up)
      (initPositionOf n.toNat (listDests m.toNat dest)) := by
    rw [htn]; exact planR_ctor up hm hn hd
  have h := sim_lowest hs hp (lowOk_ctor u up hm hn hd) l
  rw [listEnv_n target spilled hn] at h
  unfold permute_at_lowest_height
  rw [ite_eq_right hg]
  exact rel_outOf h

end FlatShuffler.Flat
