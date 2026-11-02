module

public import FlatShuffler.Kit
import all FlatShuffler.Kit

@[expose] public section
/-!
Memory lemmas for `swapWith`: stores of 1, 4 and 8 bytes, and the low 6 bytes of a word.
-/
namespace FlatShuffler.SwapWithFn

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

/-! ## Disjoint regions -/

-- Two accesses in two disjoint regions do not overlap. The regions are `[B1, B1 + l1)` and
-- `[B2, B2 + l2)`, as distances modulo `2 ^ 64`.
theorem region_sep {a b B1 B2 : Addr} {n k l1 l2 : Nat}
    (hs : l1 ≤ (B2 - B1).toNat ∧ l2 ≤ (B1 - B2).toNat) (hn : 0 < n) (hk : 0 < k)
    (ha : (a - B1).toNat + n ≤ l1) (hb : (b - B2).toNat + k ≤ l2) :
    n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat := by
  bv_omega

theorem region_sep' {a b B1 B2 : Addr} {n k l1 l2 : Nat}
    (hs : l2 ≤ (B1 - B2).toNat ∧ l1 ≤ (B2 - B1).toNat) (hn : 0 < n) (hk : 0 < k)
    (ha : (a - B1).toNat + n ≤ l1) (hb : (b - B2).toNat + k ≤ l2) :
    n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat :=
  region_sep ⟨hs.2, hs.1⟩ hn hk ha hb

-- Two accesses in one region, with the offsets from the base `B`.
theorem same_sep {a b B : Addr} {n k : Nat} (hn : 0 < n) (ha : (a - B).toNat + n ≤ (b - B).toNat)
    (hb : (b - B).toNat + k ≤ 2 ^ 64) :
    n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat := by
  bv_omega

theorem same_sep' {a b B : Addr} {n k : Nat} (hk : 0 < k) (hb : (b - B).toNat + k ≤ (a - B).toNat)
    (ha : (a - B).toNat + n ≤ 2 ^ 64) :
    n ≤ (b - a).toNat ∧ k ≤ (a - b).toNat := by
  bv_omega

/-! ## Offsets from a base -/

theorem sub_base₁ (B X : Addr) : B + X - B = X := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem sub_base₂ (B X Y : Addr) : B + X + Y - B = X + Y := by
  rw [BitVec.add_assoc, sub_base₁]

theorem sub_lit (X : Addr) (a b : Nat) :
    X - BitVec.ofNat 64 a - BitVec.ofNat 64 b = X - BitVec.ofNat 64 (a + b) := by
  bv_omega

theorem add_lit (X : Addr) (a b : Nat) :
    X + BitVec.ofNat 64 a + BitVec.ofNat 64 b = X + BitVec.ofNat 64 (a + b) := by
  bv_omega

theorem sub_sub_base (X Y Z : Addr) : X - Y - (X - Z) = Z - Y := by
  bv_omega

theorem toNat_add_lt {X : Addr} {k : Nat} (h : X.toNat + k < 2 ^ 64) :
    (X + BitVec.ofNat 64 k).toNat = X.toNat + k := by
  bv_omega

theorem toNat_mul8 {r : Word} (h : r.toNat < 2 ^ 61) : (r * 8#64).toNat = 8 * r.toNat := by
  bv_omega

theorem toNat_pred8 {L : Word} (h0 : 0 < L.toNat) (h : L.toNat < 2 ^ 61) :
    ((L + -1#64) * 8#64).toNat = 8 * L.toNat - 8 := by
  bv_omega

theorem toNat_mul12 {N : Word} (h : N.toNat < 2 ^ 60) :
    ((N + N * 2#64) * 4#64).toNat = 12 * N.toNat := by
  bv_omega

/-- An offset from a base, in `Nat`: the facts on the `toNat` of the scaled indices must be in
the context. -/
macro "in_omega" : tactic => `(tactic| ((try simp (disch := omega) only [sub_base₁, sub_base₂,
  sub_sub_base, sub_lit, BitVec.sub_self, Nat.reduceAdd, BitVec.reduceSub, toNat_add_lt,
  BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt]) <;> omega))

/-! ## The values of the stores -/

-- The low bytes of a store of a value that `movl` or `movb` takes from a load.
theorem mod32 (x : Int) : (BitVec.ofInt 32 x).toInt % 2 ^ 32 % 2 ^ 32 = x % 2 ^ 32 := by
  rw [Int.emod_emod, BitVec.toInt_ofInt]
  exact_mod_cast Int.bmod_emod (x := x) (m := 2 ^ 32)

theorem take_setWidth (z : BitVec 8) : (BitVec.setWidth 64 (BitVec.setWidth 32 z)).take 8 = z := by
  unfold BitVec.take
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have := z.isLt
  omega

theorem mod8 (y : Int) :
    ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 y))).take 8).toInt % 2 ^ 8 % 2 ^ 8
      = y % 2 ^ 8 := by
  rw [take_setWidth, Int.emod_emod, BitVec.toInt_ofInt]
  exact_mod_cast Int.bmod_emod (x := y) (m := 2 ^ 8)

-- The depth byte of the operation.
theorem take_sub {L r : BitVec 64} (h : r.toNat + 1 ≤ L.toNat) :
    (L - r - 1#64).take 8 = BitVec.ofNat 8 (L.toNat - 1 - r.toNat) := by
  unfold BitVec.take
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  bv_omega

-- The offset of the operation `N`.
theorem ofNat12 (N : BitVec 64) : BitVec.ofNat 64 (12 * N.toNat) = (N + N * 2#64) * 4#64 := by
  bv_omega

-- The junk slot of a swap: kind 1 and opcode 5 in the bytes 4 and 5.
theorem junk_eq : StackSlot.junk = StackSlot.ofWord (BitVec.ofNat 64 (2 ^ 32 + 5 * 2 ^ 40)) := by
  decide

end FlatShuffler.SwapWithFn
