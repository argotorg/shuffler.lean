import BbuKraken.Kit
import PermuteKraken.Proof

/-!
Memory lemmas for `permuteDestinations`: stores of 1, 4 and 8 bytes, the low 6 bytes of
a word, and one iteration of the swap loop `.LB55`.
-/

open PermuteKraken

namespace Bbu.FinishMem

/-! ## The depths of `permute` -/

theorem trace_depth (p : Perm) : ∀ k ≤ steps p, ∀ x ∈ p.trace k, 1 ≤ x ∧ x < p.toList.length := by
  intro k
  induction k with
  | zero => simp [Perm.trace]
  | succ k ih =>
    intro hk x hx
    rw [Perm.trace_succ, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (by omega) x hx
    · obtain ⟨idx, pos, hs⟩ := Perm.isSwap_iff.mp (p.step_state_lt k (by omega))
      rw [Perm.depth_eq _ hs]
      have := Perm.step_swap _ hs
      rw [Perm.length_state] at this
      omega

theorem permute_depth {p : Perm} {L : List Nat} (h : permute p = .ok L) :
    ∀ x ∈ L, 1 ≤ x ∧ x < p.toList.length := by
  rw [Perm.permute_eq] at h
  split at h
  · cases h
  · cases h
    exact trace_depth p _ (Nat.le_refl _)

/-! ## Stores -/

section
variable {m : Mem 64}

-- A store does not change a load that it does not overlap.
theorem load_store_off {a b : Addr} {n k : Nat} (v : Int)
    (h : n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat) :
    (m.storeInt a n v).loadInt b k = m.loadInt b k :=
  Mem.loadInt_congr fun i hi => Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => by bv_omega

theorem rd_store_off {a b : Addr} {n : Nat} (v : Int) (h : n ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :
    rd (m.storeInt a n v) b = rd m b := by
  rw [rd, rd, load_store_off v h]

theorem rdb_store_off {a b : Addr} {n : Nat} (v : Int) (h : n ≤ (b - a).toNat ∧ 1 ≤ (a - b).toNat) :
    rdb (m.storeInt a n v) b = rdb m b := by
  rw [rdb, rdb, load_store_off v h]

-- A load of the bytes of a store.
theorem load_store_same {a b : Addr} {n : Nat} (v : Int) (h : a = b) (hn : n ≤ 8) :
    (m.storeInt a n v).loadInt b n = some (v % 2 ^ (8 * n)) := by
  subst h
  rw [Mem.loadInt_storeInt _ _ _ _ (by omega), ofBytes_toBytes]

theorem rdb_store_same {a b : Addr} (v : Int) (h : a = b) :
    rdb (m.storeInt a 1 v) b = BitVec.ofInt 8 v := by
  rw [rdb, load_store_same v h (by decide), Option.get!_some]
  exact BitVec.eq_of_toInt_eq (by simpa [BitVec.toInt_ofInt] using Int.emod_bmod v 256)

end

/-! ## The low 6 bytes of a word -/

-- Two words with the same low 6 bytes give the same slot.
theorem ofWord_of_mod {a b : Word} (h : a.toNat % 2 ^ 48 = b.toNat % 2 ^ 48) :
    StackSlot.ofWord a = StackSlot.ofWord b := by
  rw [ofWord_bits]
  intro j hj
  have := congrArg (·.testBit j) h
  simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and] at this
  simpa [BitVec.getLsbD] using this

theorem get_some {m : Mem 64} {a : Addr} {n : Nat} (h : (m.loadInt a n).isSome) {i : Nat} (hi : i < n) :
    ∃ b, m.get? (a + BitVec.ofNat 64 i) = some b := by
  simp only [Mem.loadInt, Mem.loadBytes, List.allSome, Option.isSome_map] at h
  exact Option.isSome_iff_exists.mp
    (mapM_id_isSome h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

-- The low 6 bytes of a word: a load of 4 bytes and two loads of 1 byte.
theorem low48 {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome) :
    (rd m a).toNat % 2 ^ 48 = ((m.loadInt a 4).get! % 2 ^ 32
      + 2 ^ 32 * ((m.loadInt (a + 4#64) 1).get! % 2 ^ 8)
      + 2 ^ 40 * ((m.loadInt (a + 5#64) 1).get! % 2 ^ 8)).toNat := by
  obtain ⟨b0, h0⟩ := get_some h (i := 0) (by decide)
  obtain ⟨b1, h1⟩ := get_some h (i := 1) (by decide)
  obtain ⟨b2, h2⟩ := get_some h (i := 2) (by decide)
  obtain ⟨b3, h3⟩ := get_some h (i := 3) (by decide)
  obtain ⟨b4, h4⟩ := get_some h (i := 4) (by decide)
  obtain ⟨b5, h5⟩ := get_some h (i := 5) (by decide)
  obtain ⟨b6, h6⟩ := get_some h (i := 6) (by decide)
  obtain ⟨b7, h7⟩ := get_some h (i := 7) (by decide)
  simp only [BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [rd, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil,
    BitVec.add_zero, BitVec.add_assoc, h0, h1, h2, h3, h4, h5, h6, h7,
    List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.map_some,
    Option.get!_some, Int.ofBytes, List.foldr_cons, List.foldr_nil, BitVec.toNat_ofInt]
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  omega

theorem bmod_emod (w : Int) (k : Nat) : w.bmod (2 ^ k) % 2 ^ k = w % 2 ^ k := by
  simpa using Int.bmod_emod (x := w) (m := 2 ^ k)

-- The byte that `movzbl` and `movb` move.
theorem take8_emod (w : Int) :
    ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 w))).take 8).toInt % 2 ^ 8 = w % 2 ^ 8 := by
  rw [BitVec.toInt_eq_toNat_bmod, bmod_emod]
  simp [BitVec.take]
  omega

theorem ofInt32_emod (w : Int) : (BitVec.ofInt 32 w).toInt % 2 ^ 32 = w % 2 ^ 32 := by
  rw [BitVec.toInt_ofInt, bmod_emod]

/-! ## Unchanged memory -/

theorem uo_store {l : List (Addr × Nat)} {m : Mem 64} {a : Addr} {n : Nat}
    (h : Mem.Blocks.Inside a n l) (v : Int) : Mem.UnchangedOutside l m (m.storeInt a n v) :=
  Mem.UnchangedOutside.storeInt (fun _ _ => rfl) h v

theorem load_congr {l : List (Addr × Nat)} {m m' : Mem 64} {a : Addr} {n : Nat}
    (h : Mem.UnchangedOutside l m m') (ha : Mem.Blocks.Disjoint [(a, n)] l) :
    m'.loadInt a n = m.loadInt a n :=
  Mem.loadInt_congr fun _ hi => h _ (ha _ ((Mem.Blocks.Inside.base (bs := []) (Nat.le_refl n)).add_ofNat hi))

theorem disj_of {a b : Addr} {n k : Nat} (h : n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat) :
    Mem.Blocks.Disjoint [(a, n)] [(b, k)] := by
  intro x hx hy
  simp only [Mem.Blocks.Inside, or_false] at hx hy
  bv_omega

theorem disj_cons {a : Addr} {n : Nat} {p : Addr × Nat} {l : List (Addr × Nat)}
    (h1 : Mem.Blocks.Disjoint [(a, n)] [p]) (h2 : Mem.Blocks.Disjoint [(a, n)] l) :
    Mem.Blocks.Disjoint [(a, n)] (p :: l) :=
  fun x hx hy => hy.elim (fun h => h1 x hx (Or.inl h)) (h2 x hx)

theorem disj_nil {a : Addr} {n : Nat} : Mem.Blocks.Disjoint [(a, n)] [] := fun _ _ h => h

/-! ## One iteration of `.LB55` -/

-- The forms that `bbu_norm` gives for the stores of `.LB55`. `x` is `rbx`, `d`
-- the address of the depth.
def swD (m : Mem 64) (a : Addr) : Word :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Mem.loadInt m a 1).get!))

def swA (m : Mem 64) (x r10 d : Addr) : Addr := rd m (x + 64#64) + (r10 - swD m d) * 8#64

def swM1 (m : Mem 64) (x r10 rsi d : Addr) : Mem 64 :=
  Mem.storeInt m (swA m x r10 d) 8 (BitVec.toInt (rd m (rd m (x + 64#64) + rsi)))

def swB (m : Mem 64) (x r10 rsi d : Addr) : Addr := rd (swM1 m x r10 rsi d) (x + 64#64) + rsi

def swM2 (m : Mem 64) (x r10 rsi d : Addr) : Mem 64 :=
  (swM1 m x r10 rsi d).storeInt (swB m x r10 rsi d) 4
    (BitVec.ofInt 32 (Mem.loadInt m (swA m x r10 d) 4).get!).toInt

def swM3 (m : Mem 64) (x r10 rsi d : Addr) : Mem 64 :=
  (swM2 m x r10 rsi d).storeInt (swB m x r10 rsi d + 4#64) 1
    ((swD m (swA m x r10 d + 4#64)).take 8).toInt

def swM4 (m : Mem 64) (x r10 rsi d : Addr) : Mem 64 :=
  (swM3 m x r10 rsi d).storeInt (swB m x r10 rsi d + 5#64) 1
    ((swD m (swA m x r10 d + 5#64)).take 8).toInt

def swO (M : Mem 64) (x : Addr) : Addr :=
  rd M (x + 48#64) + (rd M (x + 16#64) + rd M (x + 16#64) * 2#64) * 4#64

def swOp (M : Mem 64) (x d : Addr) : Mem 64 :=
  ((((M.storeInt (swO M x) 1 0).storeInt (swO M x + 1#64) 1 ((swD M d).take 8).toInt).storeInt
    (swO M x + 4#64) 4 0).storeInt (swO M x + 8#64) 1 1).storeInt (swO M x + 9#64) 1 5

def swCnt (M : Mem 64) (x : Addr) : Mem 64 :=
  M.storeInt (x + 16#64) 8 (1#64 + rd M (x + 16#64)).toInt

def swMem (m : Mem 64) (x r10 rsi d : Addr) : Mem 64 :=
  swCnt (swOp (swM4 m x r10 rsi d) x d) x

-- The hypotheses of one iteration: swap the top slot with the slot `d` below it.
structure SwHyp (m : Mem 64) (S r10 rsi da : Addr) (d : Nat) : Prop where
  wf : Wf m S
  hr10 : r10 = rd m (wordAt S 0) - 1#64
  hrsi : rsi = r10 * 8#64
  d1 : 1 ≤ d
  d2 : d < (rd m (wordAt S 0)).toNat
  hc : (rd m (wordAt S 2)).toNat < 6 * nOf m S
  hD : swD m da = BitVec.ofNat 64 d
  hda : Mem.Blocks.Disjoint [(da, 1)] (writable m S)

section
variable {m : Mem 64} {S r10 rsi da : Addr} {d : Nat}

theorem data_def : rd m (S + 64#64) = dataOf m S := rfl

-- The facts on addresses for `bv_omega`.
theorem SwHyp.facts (h : SwHyp m S r10 rsi da d) :
    S.toNat + 8 * 2057 ≤ 2 ^ 64 ∧ (dataOf m S).toNat + 8 * nOf m S ≤ 2 ^ 64
      ∧ (opsOf m S).toNat + 72 * nOf m S ≤ 2 ^ 64
      ∧ ((dataOf m S).toNat + 8 * nOf m S ≤ S.toNat ∨ S.toNat + 8 * 2057 ≤ (dataOf m S).toNat)
      ∧ ((opsOf m S).toNat + 72 * nOf m S ≤ S.toNat ∨ S.toNat + 8 * 2057 ≤ (opsOf m S).toNat)
      ∧ ((dataOf m S).toNat + 8 * nOf m S ≤ (opsOf m S).toNat
        ∨ (opsOf m S).toNat + 72 * nOf m S ≤ (dataOf m S).toNat)
      ∧ (rd m (wordAt S 0)).toNat ≤ nOf m S ∧ nOf m S ≤ 1024 := by
  have hw := h.wf
  have := h.d2
  have hn : 0 < nOf m S := by have := hw.len_le; omega
  exact ⟨hw.struct_lt, hw.data_lt, hw.ops_lt, hw.sep_data hn, hw.sep_ops hn, hw.sep_data_ops hn,
    hw.len_le, hw.n_le⟩

theorem SwHyp.A (h : SwHyp m S r10 rsi da d) :
    swA m S r10 da = wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d) := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  have := h.d1; have := h.d2
  rw [swA, h.hD, h.hr10, data_def]
  bv_omega

theorem SwHyp.data1 (h : SwHyp m S r10 rsi da d) :
    rd (swM1 m S r10 rsi da) (S + 64#64) = dataOf m S := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  have := h.d1; have := h.d2
  rw [swM1, h.A, rd_store_off _ (by bv_omega)]
  rfl

theorem SwHyp.B (h : SwHyp m S r10 rsi da d) :
    swB m S r10 rsi da = wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1) := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  have := h.d1; have := h.d2
  rw [swB, h.data1, h.hrsi, h.hr10]
  bv_omega


-- The addresses as numbers, for `omega`.
theorem SwHyp.nat (h : SwHyp m S r10 rsi da d) :
    (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d)).toNat
        = (dataOf m S).toNat + 8 * ((rd m (wordAt S 0)).toNat - 1 - d)
      ∧ (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1)).toNat
        = (dataOf m S).toNat + 8 * ((rd m (wordAt S 0)).toNat - 1)
      ∧ (opAt m S (rd m (wordAt S 2)).toNat).toNat = (opsOf m S).toNat + 12 * (rd m (wordAt S 2)).toNat
      ∧ (S + 16#64).toNat = S.toNat + 16 := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  have := h.d1; have := h.d2; have := h.hc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem SwHyp.uo4 (_h : SwHyp m S r10 rsi da d) :
    Mem.UnchangedOutside [(swA m S r10 da, 8), (swB m S r10 rsi da, 8)] m (swM4 m S r10 rsi da) := by
  simp only [swM4, swM3, swM2, swM1]
  refine (((uo_store (l := [(swA m S r10 da, 8), (swB m S r10 rsi da, 8)]) (Or.inl ?_) _).storeInt
    (Or.inr (Or.inl ?_)) _).storeInt (Or.inr (Or.inl ?_)) _).storeInt (Or.inr (Or.inl ?_)) _ <;> bv_omega

-- The address of the new operation.
theorem SwHyp.O (h : SwHyp m S r10 rsi da d) :
    swO (swM4 m S r10 rsi da) S = opAt m S (rd m (wordAt S 2)).toNat := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, -, -⟩ := h.nat
  have := h.d1; have := h.d2; have := h.hc
  have hu := h.uo4
  rw [h.A, h.B] at hu
  have e48 : rd (swM4 m S r10 rsi da) (S + 48#64) = opsOf m S :=
    rd_congr hu (disj_cons (disj_of (by bv_omega)) (disj_cons (disj_of (by bv_omega)) disj_nil))
  have e16 : rd (swM4 m S r10 rsi da) (S + 16#64) = rd m (wordAt S 2) :=
    rd_congr hu (disj_cons (disj_of (by bv_omega)) (disj_cons (disj_of (by bv_omega)) disj_nil))
  rw [swO, e48, e16]
  bv_omega

theorem SwHyp.uoHi (h : SwHyp m S r10 rsi da d) :
    Mem.UnchangedOutside [(opAt m S (rd m (wordAt S 2)).toNat, 12), (wordAt S 2, 8)]
      (swM4 m S r10 rsi da) (swMem m S r10 rsi da) := by
  simp only [swMem, swCnt, swOp, h.O]
  refine (((((uo_store (l := [(opAt m S (rd m (wordAt S 2)).toNat, 12), (wordAt S 2, 8)]) (Or.inl ?_)
    _).storeInt (Or.inl ?_) _).storeInt (Or.inl ?_) _).storeInt (Or.inl ?_) _).storeInt (Or.inl ?_)
    _).storeInt (Or.inr (Or.inl ?_)) _ <;> bv_omega

theorem mapped_swM4 {l : List (Addr × Nat)} (hm : Mem.Mapped l m) :
    Mem.Mapped l (swM4 m S r10 rsi da) := by
  simp only [swM4, swM3, swM2, swM1]
  repeat apply Mem.Mapped.storeInt
  exact hm

theorem mapped_swMem {l : List (Addr × Nat)} (hm : Mem.Mapped l m) :
    Mem.Mapped l (swMem m S r10 rsi da) := by
  simp only [swMem, swCnt, swOp]
  repeat apply Mem.Mapped.storeInt
  exact hm

-- The count of operations.
theorem SwHyp.cnt (h : SwHyp m S r10 rsi da d) :
    rd (swMem m S r10 rsi da) (wordAt S 2) = 1#64 + rd m (wordAt S 2) := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, nO, n16⟩ := h.nat
  have := h.d1; have := h.d2; have := h.hc
  have hu := h.uo4
  rw [h.A, h.B] at hu
  have e16 : rd (swM4 m S r10 rsi da) (S + 16#64) = rd m (wordAt S 2) :=
    rd_congr hu (disj_cons (disj_of (by bv_omega)) (disj_cons (disj_of (by bv_omega)) disj_nil))
  simp only [swMem, swCnt, swOp, h.O]
  rw [rd_store_same _ rfl, BitVec.ofInt_toInt]
  simp (disch := first | bv_omega | fail) only [rd_store_off]
  rw [e16]

theorem load_store_self {m : Mem 64} {a : Addr} {n : Nat} (v : Int) (hn : n ≤ 8) :
    (m.storeInt a n v).loadInt a n = some (v % 2 ^ (8 * n)) :=
  load_store_same v rfl hn

-- The slot `top - d` gets the top slot.
theorem SwHyp.lo (h : SwHyp m S r10 rsi da d) :
    rd (swM4 m S r10 rsi da) (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d))
      = rd m (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1)) := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, -, -⟩ := h.nat
  have := h.d1; have := h.d2
  simp only [swM4, swM3, swM2, swM1, h.A, h.B, data_def]
  simp (disch := first | bv_omega | fail) only [rd_store_off]
  rw [rd_store_same _ rfl, BitVec.ofInt_toInt, h.hrsi, h.hr10]
  congr 1
  bv_omega

-- The top slot gets the slot `top - d`.
theorem SwHyp.hi (h : SwHyp m S r10 rsi da d) :
    StackSlot.ofWord (rd (swM4 m S r10 rsi da) (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1)))
      = StackSlot.ofWord (rd m (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d))) := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, -, -⟩ := h.nat
  have := h.d1; have := h.d2
  have hin : ∀ k < (rd m (wordAt S 0)).toNat,
      Mem.Blocks.Inside (wordAt (dataOf m S) k) 8 (writable m S ++ readable m S) := fun k hk =>
    inside_append.mpr (Or.inl (inside_writable (Or.inr (Or.inr (Or.inl (by bv_omega))))))
  have sA := h.wf.mapped.loadInt_isSome (hin ((rd m (wordAt S 0)).toNat - 1 - d) (by omega))
  have sB := (mapped_swM4 (r10 := r10) (rsi := rsi) (da := da) (S := S) h.wf.mapped).loadInt_isSome
    (hin ((rd m (wordAt S 0)).toNat - 1) (by omega))
  apply ofWord_of_mod
  rw [low48 sA, low48 sB]
  simp only [swM4, swM3, swM2, swM1, h.A, h.B]
  simp (disch := first | decide | bv_omega | fail) only [load_store_off, load_store_self, Option.get!_some]
  simp only [Nat.reduceMul, Int.emod_emod, ofInt32_emod, swD, take8_emod]

theorem inside_subset {x : Addr} {n : Nat} {l1 l2 : List (Addr × Nat)} (h : ∀ p ∈ l1, p ∈ l2)
    (hx : Mem.Blocks.Inside x n l1) : Mem.Blocks.Inside x n l2 := by
  induction l1 with
  | nil => exact hx.elim
  | cons p l1 ih =>
    obtain ⟨a, k⟩ := p
    rcases hx with hx | hx
    · exact inside_of_mem (h _ List.mem_cons_self) (Or.inl hx)
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) hx

theorem uo_mono {l l' : List (Addr × Nat)} {m m' : Mem 64} (h : Mem.UnchangedOutside l m m')
    (hs : ∀ x, Mem.Blocks.Inside x 1 l → Mem.Blocks.Inside x 1 l') : Mem.UnchangedOutside l' m m' :=
  fun b hb => h b fun hin => hb (hs b hin)

theorem uo_trans {l : List (Addr × Nat)} {m m' m'' : Mem 64} (h : Mem.UnchangedOutside l m m')
    (h' : Mem.UnchangedOutside l m' m'') : Mem.UnchangedOutside l m m'' :=
  fun b hb => (h' b hb).trans (h b hb)

/-! Address facts as numbers: with these `omega` needs no `% 2 ^ 64`. -/

theorem toNat_add_of {a : Addr} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  bv_omega

theorem off_le {a b : Addr} {n k : Nat} (h1 : b.toNat ≤ a.toNat) (h2 : a.toNat + n ≤ b.toNat + k) :
    (a - b).toNat + n ≤ k := by
  bv_omega

theorem disj_sep {a b : Addr} {n k : Nat} (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat)
    (ha : a.toNat + n ≤ 2 ^ 64) (hb : b.toNat + k ≤ 2 ^ 64) :
    Mem.Blocks.Disjoint [(a, n)] [(b, k)] := by
  intro x hx hy
  simp only [Mem.Blocks.Inside, or_false] at hx hy
  bv_omega

local macro "dj" : tactic => `(tactic| exact disj_sep (by omega) (by omega) (by omega))

local macro "disj2" : tactic => `(tactic|
  exact disj_cons (by dj) (disj_cons (by dj) disj_nil))

local macro "disj4" : tactic => `(tactic|
  exact disj_cons (by dj) (disj_cons (by dj) (disj_cons (by dj) (disj_cons (by dj) disj_nil))))

theorem SwHyp.word (h : SwHyp m S r10 rsi da d) {k : Nat} (hk : k < 2057) :
    (wordAt S k).toNat = S.toNat + 8 * k := by
  obtain ⟨hs, -⟩ := h.facts
  exact toNat_add_of (by omega)

theorem SwHyp.slot (h : SwHyp m S r10 rsi da d) {k : Nat} (hk : k < (rd m (wordAt S 0)).toNat) :
    (wordAt (dataOf m S) k).toNat = (dataOf m S).toNat + 8 * k := by
  obtain ⟨-, hdl, -, -, -, -, hlen, -⟩ := h.facts
  exact toNat_add_of (by omega)

theorem SwHyp.opk (h : SwHyp m S r10 rsi da d) {k j : Nat} (hk : k ≤ (rd m (wordAt S 2)).toNat)
    (hj : j < 12) : (opAt m S k + BitVec.ofNat 64 j).toNat = (opsOf m S).toNat + 12 * k + j := by
  obtain ⟨-, -, hol, -⟩ := h.facts
  have := h.hc
  have e : (opAt m S k).toNat = (opsOf m S).toNat + 12 * k := toNat_add_of (by omega)
  rw [toNat_add_of (by omega), e]

theorem SwHyp.uoAll (h : SwHyp m S r10 rsi da d) :
    Mem.UnchangedOutside [(wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d), 8),
      (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1), 8),
      (opAt m S (rd m (wordAt S 2)).toNat, 12), (wordAt S 2, 8)] m (swMem m S r10 rsi da) := by
  have ulo := h.uo4
  rw [h.A, h.B] at ulo
  exact uo_trans (uo_mono ulo fun _ => inside_subset (by simp)) (uo_mono h.uoHi fun _ => inside_subset (by simp))

-- The new operation is `swap d`.
theorem SwHyp.op (h : SwHyp m S r10 rsi da d) :
    rdb (swMem m S r10 rsi da) (opAt m S (rd m (wordAt S 2)).toNat) = Swap
      ∧ rdb (swMem m S r10 rsi da) (opAt m S (rd m (wordAt S 2)).toNat + 1#64) = BitVec.ofNat 8 d
      ∧ StackSlot.ofWord (rd (swMem m S r10 rsi da) (opAt m S (rd m (wordAt S 2)).toNat + 4#64))
        = StackSlot.junk := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, nO, n16⟩ := h.nat
  have := h.d1; have := h.d2; have := h.hc
  have n4 := h.opk (Nat.le_refl _) (j := 4) (by decide)
  have ulo := h.uo4
  rw [h.A, h.B] at ulo
  have hwr : ∀ x, Mem.Blocks.Inside x 1 [(wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d), 8),
      (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1), 8)] → Mem.Blocks.Inside x 1 (writable m S) :=
    fun x hx => hx.elim
      (fun hx => Kit.inside_bytes (inside_writable (Or.inr (Or.inr (Or.inl (off_le (by omega) (by omega))))))
        x (Or.inl hx))
      fun hx => hx.elim
        (fun hx => Kit.inside_bytes (inside_writable (Or.inr (Or.inr (Or.inl (off_le (by omega) (by omega))))))
          x (Or.inl hx))
        False.elim
  have hdD : swD (swM4 m S r10 rsi da) da = BitVec.ofNat 64 d := by
    rw [swD, load_congr ulo (fun x hx hy => h.hda x hx (hwr x hy))]
    exact h.hD
  have sO : ((swMem m S r10 rsi da).loadInt (opAt m S (rd m (wordAt S 2)).toNat + 4#64) 8).isSome :=
    (mapped_swMem h.wf.mapped).loadInt_isSome (inside_append.mpr (Or.inl (inside_writable
      (Or.inr (Or.inr (Or.inr (Or.inl (off_le (by omega) (by omega)))))))))
  clear hwr ulo
  refine ⟨?_, ?_, ?_⟩
  · simp only [swMem, swCnt, swOp, h.O]
    simp (disch := first | bv_omega | fail) only [rdb_store_off]
    rw [rdb_store_same _ rfl]
    rfl
  · simp only [swMem, swCnt, swOp, h.O]
    simp (disch := first | bv_omega | fail) only [rdb_store_off]
    rw [rdb_store_same _ rfl, hdD, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.take]
  · refine (ofWord_of_mod (b := BitVec.ofNat 64 (2 ^ 32 + 5 * 2 ^ 40)) ?_).trans (by decide)
    rw [low48 sO]
    simp only [swMem, swCnt, swOp, h.O]
    simp (disch := first | decide | bv_omega | fail) only [load_store_off, load_store_same,
      Option.get!_some]
    decide

-- One iteration of `.LB55` does `swapTop`.
theorem SwHyp.st (h : SwHyp m S r10 rsi da d) :
    stOf (swMem m S r10 rsi da) S = swapTop (stOf m S) d := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, nO, -⟩ := h.nat
  have := h.d1; have := h.d2; have hc := h.hc
  have U := h.uoAll
  have uhi := h.uoHi
  have n2 := h.word (k := 2) (by decide)
  have word : ∀ k < 2057, k ≠ 2 → rd (swMem m S r10 rsi da) (wordAt S k) = rd m (wordAt S k) :=
    fun k hk hk2 => by
      have := h.word hk
      exact rd_congr U (by disj4)
  have e0 := word 0 (by decide) (by decide)
  have e1 := word 1 (by decide) (by decide)
  have e3 := word 3 (by decide) (by decide)
  have e6 : opsOf (swMem m S r10 rsi da) S = opsOf m S := word 6 (by decide) (by decide)
  have e8 : dataOf (swMem m S r10 rsi da) S = dataOf m S := word 8 (by decide) (by decide)
  refine stOf_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [e0]; simp [swapTop, St.len, stOf]
  · rw [e1]; rfl
  · rw [h.cnt]; simp only [swapTop, stOf, List.length_append, List.length_map, List.length_range,
      List.length_singleton]
    bv_omega
  · intro i hi
    have hi' : i < (rd m (wordAt S 0)).toNat := by simpa [swapTop, St.len, stOf] using hi
    have ni := h.slot hi'
    have edest := word (DEST + i) (by simp only [DEST_eq]; omega) (by simp only [DEST_eq]; omega)
    simp only [swapTop, List.getElem_set]
    simp only [slotOf, e8, edest, len_stOf]
    split
    · next ht =>
      subst ht
      rw [rd_congr uhi (by disj2), h.hi, val_stOf (by omega), dest_stOf (by omega)]
    · split
      · next hb =>
        subst hb
        rw [rd_congr uhi (by disj2), h.lo, val_stOf (by omega), dest_stOf (by omega)]
      · rw [rd_congr U (by disj4)]
        simp [stOf, slotOf]
  · simp [swapTop, stOf, nOf, e3]
  · intro k hk
    have hk' : k < nOf m S := by simpa [swapTop, stOf] using hk
    have ek := word (POS + k) (by simp only [POS_eq]; omega) (by simp only [POS_eq]; omega)
    simp [swapTop, stOf, ek]
  · intro i hi
    have hi' : i < (rd m (wordAt S 2)).toNat + 1 := by simpa [swapTop, stOf] using hi
    simp only [swapTop, List.getElem_append]
    simp only [nops_stOf]
    split
    · next hic =>
      have o0 := h.opk (k := i) (by omega) (j := 0) (by decide)
      have o1 := h.opk (k := i) (by omega) (j := 1) (by decide)
      have o4 := h.opk (k := i) (by omega) (j := 4) (by decide)
      simp only [BitVec.add_zero, opAt] at o0 o1 o4
      simp only [opOf, opAt, e6]
      rw [rdb_congr U (by disj4), rdb_congr U (by disj4), rd_congr U (by disj4)]
      simp [stOf, opOf]
    · have hic' : i = (rd m (wordAt S 2)).toNat := by omega
      subst hic'
      obtain ⟨o1, o2, o3⟩ := h.op
      simp only [opOf, opAt, e6] at o1 o2 o3 ⊢
      simp [o1, o2, o3, Op.swap]


-- The loads of one iteration of `.LB55` succeed.
theorem SwHyp.some (h : SwHyp m S r10 rsi da d)
    (hm : Mem.Mapped ((da, 1) :: (writable m S ++ readable m S)) m) :
    (m.loadInt (S + 64#64) 8).isSome ∧ (m.loadInt da 1).isSome
      ∧ (m.loadInt (swA m S r10 da) 4).isSome ∧ (m.loadInt (swA m S r10 da + 4#64) 1).isSome
      ∧ (m.loadInt (swA m S r10 da + 5#64) 1).isSome ∧ (m.loadInt (rd m (S + 64#64) + rsi) 8).isSome
      ∧ (m.loadInt (swA m S r10 da) 8).isSome ∧ (m.loadInt (swB m S r10 rsi da) 4).isSome
      ∧ (m.loadInt (swB m S r10 rsi da + 4#64) 1).isSome ∧ (m.loadInt (swB m S r10 rsi da + 5#64) 1).isSome
      ∧ (m.loadInt (S + 16#64) 8).isSome ∧ (m.loadInt (S + 48#64) 8).isSome
      ∧ (m.loadInt (swO (swM4 m S r10 rsi da) S) 1).isSome
      ∧ (m.loadInt (swO (swM4 m S r10 rsi da) S + 1#64) 1).isSome
      ∧ (m.loadInt (swO (swM4 m S r10 rsi da) S + 4#64) 4).isSome
      ∧ (m.loadInt (swO (swM4 m S r10 rsi da) S + 8#64) 1).isSome
      ∧ (m.loadInt (swO (swM4 m S r10 rsi da) S + 9#64) 1).isSome := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, nO, -⟩ := h.nat
  have := h.d1; have := h.d2; have := h.hc
  have hW : Mem.Mapped (writable m S ++ readable m S) m := fun x hx => hm x (Or.inr hx)
  have hw := h.wf
  -- A block of the working stack or the ops buffer.
  have hD : ∀ {a : Addr} {n : Nat}, (a - dataOf m S).toNat + n ≤ 8 * nOf m S → (m.loadInt a n).isSome :=
    fun hx => hW.loadInt_isSome (inside_append.mpr (Or.inl (inside_writable (Or.inr (Or.inr (Or.inl hx))))))
  have hO : ∀ {a : Addr} {n : Nat}, (a - opsOf m S).toNat + n ≤ 72 * nOf m S → (m.loadInt a n).isSome :=
    fun hx => hW.loadInt_isSome (inside_append.mpr (Or.inl (inside_writable
      (Or.inr (Or.inr (Or.inr (Or.inl hx)))))))
  have o1 := h.opk (Nat.le_refl _) (j := 1) (by decide)
  have o4 := h.opk (Nat.le_refl _) (j := 4) (by decide)
  have o8 := h.opk (Nat.le_refl _) (j := 8) (by decide)
  have o9 := h.opk (Nat.le_refl _) (j := 9) (by decide)
  have b4 : (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1) + 4#64).toNat
      = (dataOf m S).toNat + 8 * ((rd m (wordAt S 0)).toNat - 1) + 4 := by
    rw [toNat_add_of (k := 4) (by omega), nB]
  have b5 : (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1) + 5#64).toNat
      = (dataOf m S).toNat + 8 * ((rd m (wordAt S 0)).toNat - 1) + 5 := by
    rw [toNat_add_of (k := 5) (by omega), nB]
  have a4 : (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d) + 4#64).toNat
      = (dataOf m S).toNat + 8 * ((rd m (wordAt S 0)).toNat - 1 - d) + 4 := by
    rw [toNat_add_of (k := 4) (by omega), nA]
  have a5 : (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d) + 5#64).toNat
      = (dataOf m S).toNat + 8 * ((rd m (wordAt S 0)).toNat - 1 - d) + 5 := by
    rw [toNat_add_of (k := 5) (by omega), nA]
  have e6 : rd m (S + 64#64) + rsi = wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1) := by
    rw [data_def, h.hrsi, h.hr10]
    bv_omega
  rw [h.O, h.A, h.B, e6]
  exact ⟨hw.word_isSome hW (k := 8) (by decide), hm.loadInt_isSome (Or.inl (by simp)),
    hD (off_le (by omega) (by omega)), hD (off_le (by omega) (by omega)),
    hD (off_le (by omega) (by omega)), hD (off_le (by omega) (by omega)),
    hD (off_le (by omega) (by omega)), hD (off_le (by omega) (by omega)),
    hD (off_le (by omega) (by omega)), hD (off_le (by omega) (by omega)),
    hw.word_isSome hW (k := 2) (by decide), hw.word_isSome hW (k := 6) (by decide),
    hO (off_le (by omega) (by omega)), hO (off_le (by omega) (by omega)),
    hO (off_le (by omega) (by omega)), hO (off_le (by omega) (by omega)),
    hO (off_le (by omega) (by omega))⟩

theorem inside_sub {x a b : Addr} {n k : Nat} (hx : (x - a).toNat + 1 ≤ n) (h1 : b.toNat ≤ a.toNat)
    (h2 : a.toNat + n ≤ b.toNat + k) (_h3 : a.toNat + n ≤ 2 ^ 64) : (x - b).toNat + 1 ≤ k := by
  bv_omega

-- The blocks that one iteration writes lie in the count, the working stack and the ops buffer.
theorem SwHyp.inW3 (h : SwHyp m S r10 rsi da d) :
    ∀ x, Mem.Blocks.Inside x 1 [(wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1 - d), 8),
      (wordAt (dataOf m S) ((rd m (wordAt S 0)).toNat - 1), 8),
      (opAt m S (rd m (wordAt S 2)).toNat, 12), (wordAt S 2, 8)] →
      Mem.Blocks.Inside x 1 [(wordAt S 2, 8), (dataOf m S, 8 * nOf m S), (opsOf m S, 72 * nOf m S)] := by
  obtain ⟨hs, hdl, hol, h1, h2, h3, hlen, hn⟩ := h.facts
  obtain ⟨nA, nB, nO, -⟩ := h.nat
  have := h.d1; have := h.d2; have := h.hc
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  rcases hx with hx | hx | hx | hx
  · exact Or.inr (Or.inl (inside_sub hx (by omega) (by omega) (by omega)))
  · exact Or.inr (Or.inl (inside_sub hx (by omega) (by omega) (by omega)))
  · exact Or.inr (Or.inr (inside_sub hx (by omega) (by omega) (by omega)))
  · left; exact hx

end

/-! ## Swaps in the model -/

theorem len_swapTop (st : St) (d : Nat) : (swapTop st d).len = st.len := by
  simp [swapTop, St.len]

theorem len_foldl (L : List Nat) (st : St) : (L.foldl swapTop st).len = st.len := by
  induction L generalizing st with
  | nil => rfl
  | cons d L ih => rw [List.foldl_cons, ih, len_swapTop]

theorem trace_foldl (L : List Nat) (st : St) :
    (L.foldl swapTop st).trace.length = st.trace.length + L.length := by
  induction L generalizing st with
  | nil => rfl
  | cons d L ih =>
    rw [List.foldl_cons, ih]
    simp [swapTop]
    omega

end Bbu.FinishMem
