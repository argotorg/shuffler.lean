import BbuKraken.Kit
import PermuteKraken.Proof

/-!
Memory lemmas for the old `permuteDestinations`: stores of 1, 4 and 8 bytes, the low 6 bytes of
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

def swA (m : Mem 64) (x r10 d : Addr) : Addr := rd m (x + 24#64) + (r10 - swD m d) * 8#64

def swM1 (m : Mem 64) (x r10 rsi d : Addr) : Mem 64 :=
  Mem.storeInt m (swA m x r10 d) 8 (BitVec.toInt (rd m (rd m (x + 24#64) + rsi)))

def swB (m : Mem 64) (x r10 rsi d : Addr) : Addr := rd (swM1 m x r10 rsi d) (x + 24#64) + rsi

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

theorem data_def : rd m (S + 24#64) = dataOf m S := rfl

theorem SwHyp.uo4 (_h : SwHyp m S r10 rsi da d) :
    Mem.UnchangedOutside [(swA m S r10 da, 8), (swB m S r10 rsi da, 8)] m (swM4 m S r10 rsi da) := by
  simp only [swM4, swM3, swM2, swM1]
  refine (((uo_store (l := [(swA m S r10 da, 8), (swB m S r10 rsi da, 8)]) (Or.inl ?_) _).storeInt
    (Or.inr (Or.inl ?_)) _).storeInt (Or.inr (Or.inl ?_)) _).storeInt (Or.inr (Or.inl ?_)) _ <;> bv_omega

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

theorem load_store_self {m : Mem 64} {a : Addr} {n : Nat} (v : Int) (hn : n ≤ 8) :
    (m.storeInt a n v).loadInt a n = some (v % 2 ^ (8 * n)) :=
  load_store_same v rfl hn

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

theorem inside_sub {x a b : Addr} {n k : Nat} (hx : (x - a).toNat + 1 ≤ n) (h1 : b.toNat ≤ a.toNat)
    (h2 : a.toNat + n ≤ b.toNat + k) (_h3 : a.toNat + n ≤ 2 ^ 64) : (x - b).toNat + 1 ≤ k := by
  bv_omega

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
