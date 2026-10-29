import BbuKraken.Kit

/-!
Lemmas for the body triples of `push` (`c/bbu/<Names.push>.S`) and `dup` (`c/bbu/<Names.dup>.S`).
Both read `m_positionOf[_destination]`, write the destination, the position, one
operation and the slot, and add 1 to `nops` and `len`. Neither has a frame or a call.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace PushDup
open Kit

/-! ## Reads after stores of 1, 4 and 8 bytes -/

section
variable {m : Mem 64}

theorem rd_store_off {a b : Addr} {n : Nat} (v : Int) (h : n ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) :
    rd (m.storeInt a n v) b = rd m b := by
  rw [rd, rd, Mem.loadInt_congr (m' := m)]
  intro i hi
  exact Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => by bv_omega

theorem rdb_store_off {a b : Addr} {n : Nat} (v : Int) (h : n ≤ (b - a).toNat ∧ 1 ≤ (a - b).toNat) :
    rdb (m.storeInt a n v) b = rdb m b := by
  rw [rdb, rdb, Mem.loadInt_congr (m' := m)]
  intro i hi
  exact Mem.get?_storeInt_of_ne _ _ _ _ _ fun j hj he => by bv_omega

theorem rdb_store_same {a b : Addr} (v : Int) (h : a = b) :
    rdb (m.storeInt a 1 v) b = BitVec.ofInt 8 v := by
  subst h
  rw [rdb, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some, ofBytes_toBytes, Int.take]
  simp [BitVec.ofInt]

-- Byte `i` of a store of `n` bytes.
theorem get?_store_idx (a : Addr) {n i : Nat} (v : Int) (hi : i < n) (hn : n ≤ 2 ^ 64) :
    (m.storeInt a n v).get? (a + BitVec.ofNat 64 i) = (Int.toBytes n v)[i]? := by
  have hl := Int.toBytes_length n v
  rw [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union, ← Std.ExtHashMap.get?_eq_getElem?,
    get?_At_idx _ a i (by omega) (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

theorem loadInt_bytes {a : Addr} (bs : List UInt8)
    (h : ∀ i < bs.length, m.get? (a + BitVec.ofNat 64 i) = bs[i]?) :
    m.loadInt a bs.length = some (Int.ofBytes bs) := by
  rw [Mem.loadInt, Mem.loadBytes, List.map_congr_left (fun i hi => h i (List.mem_range.mp hi)),
    List.map_range_getElem?, List.allSome_map_some]
  rfl

end

/-! ## Address arithmetic

`omega` is not complete for the `% 2 ^ 64` terms of `bv_omega`, and it can run for a very
long time on a `% 2 ^ 64` of a term that is not in `[0, 2 ^ 65)`. `addr_omega` first cancels
the common base of two addresses, then removes each `%` (a term below `2 ^ 64`, or a term in
`[2 ^ 64, 2 ^ 65)`). It fails at once if a `%` stays. -/

theorem add_sub_left' (B x : Addr) : B + x - B = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem add_sub_add_left' (B x y : Addr) : B + x - (B + y) = x - y := by bv_omega

theorem sub_add_left' (B y : Addr) : B - (B + y) = -y := by bv_omega

theorem toNat_mul_small (x : Addr) (k : Nat) (h : x.toNat * k < 2 ^ 64) :
    (x * BitVec.ofNat 64 k).toNat = x.toNat * k := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
  · simp [h0]
  · rw [Nat.mod_eq_of_lt (a := k) (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left k h0) h)]
    exact Nat.mod_eq_of_lt h

-- The address of operation `N` as the asm computes it.
theorem mul12 (N : Addr) : (N + N * 2#64) * 4#64 = N * 12#64 := by
  rw [BitVec.add_mul, BitVec.mul_assoc, ← BitVec.mul_add]; rfl

macro "addr_omega" : tactic =>
  `(tactic| ((try simp only [mul12, BitVec.add_assoc, add_sub_left', add_sub_add_left',
      sub_add_left', BitVec.sub_self, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg]) <;>
    (try simp (disch := omega) only [toNat_mul_small]) <;>
    (try simp -implicitDefEqProofs only [bitvec_to_nat]) <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;>
    (try simp (disch := omega) only [Nat.mod_eq_sub_mod]) <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;>
    (fail_if_success simp only [Nat.mod_def]) <;> omega))

-- Two accesses in two separate regions `B1` (`l1` bytes) and `B2` (`l2` bytes).
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

-- The facts of `facts` that `omega` does not need after `region_sep`.
set_option hygiene false in
macro "pd_clear" : tactic => `(tactic| ((try clear hs1) <;> (try clear hs2) <;> (try clear hs3) <;>
  (try clear hs4) <;> (try clear hs5) <;> (try clear hs6)))

-- An offset in a region: the address must have the base of the region as its first term,
-- so that `rw` fails at once for an address in another region.
macro "pd_off" : tactic => `(tactic| ((try simp only [BitVec.add_assoc]) <;>
  (first | rw [add_sub_left'] | rw [BitVec.sub_self]) <;> addr_omega))

-- The side conditions of the reads: an access in one region against an access in another
-- region (with the facts `hs1` to `hs6` of `facts`), or two accesses in the same region.
set_option hygiene false in
macro "pd_disch" : tactic => `(tactic| first
  | (refine region_sep hs1 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep' hs1 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep hs2 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep' hs2 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep hs3 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep' hs3 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep hs4 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep' hs4 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep hs5 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep' hs5 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep hs6 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (refine region_sep' hs6 ?_ ?_ ?_ ?_ <;> pd_clear <;> first | pd_off | omega)
  | (pd_clear; addr_omega)
  | fail)

/-- The reads after stores. A read at the address of a store must have the same address
term: a failed `omega` call or a failed `rfl` with unfolding is slow, so the `_same`
lemmas use only a reducible `rfl`. -/
macro "pd_rd" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| repeat (first
    | simp (disch := with_reducible rfl) only [rd_store_same, rdb_store_same, BitVec.ofInt_toInt,
        BitVec.ofInt_ofNat] $(loc)?
    | simp (disch := pd_disch) only [rd_store_off, rdb_store_off] $(loc)?))

/-! ## The addresses of the model as the asm computes them -/

theorem ofNat_mul_toNat (x : Addr) (c : Nat) :
    BitVec.ofNat 64 (c * x.toNat) = x * BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem wordAt_toNat (B x : Addr) : wordAt B x.toNat = B + x * 8#64 := by
  simp only [wordAt, ofNat_mul_toNat]

theorem wordAt_dest (S x : Addr) : wordAt S (DEST + x.toNat) = S + x * 8#64 + 56#64 := by
  simp only [wordAt, DEST_eq, Nat.mul_add, BitVec.ofNat_add, ofNat_mul_toNat, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 (8 * 7))]

theorem wordAt_pos (S x : Addr) : wordAt S (POS + x.toNat) = S + x * 8#64 + 8248#64 := by
  simp only [wordAt, POS_eq, Nat.mul_add, BitVec.ofNat_add, ofNat_mul_toNat, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 (8 * 1031))]

/-! ## The slot of an operation -/

-- A word with the bytes 0, 0, 0, 0, 1, 5 at the bottom holds the junk slot.
theorem ofWord_low {w : Word} {y : Nat} (hw : w.toNat = y * 2 ^ 48 + 5 * 2 ^ 40 + 2 ^ 32) :
    StackSlot.ofWord w = .junk := by
  simp only [StackSlot.ofWord, StackSlot.junk, Junk, Unreachable, StackSlot.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, hw]
  · show _ = 0; omega
  · show _ = 1; omega
  · show _ = 5; omega

theorem ofWord_junk {m : Mem 64} {a : Addr} (hm : Mem.Mapped [(a, 8)] m)
    (h0 : ∀ i < 4, m.get? (a + BitVec.ofNat 64 i) = some 0)
    (h4 : m.get? (a + 4#64) = some 1) (h5 : m.get? (a + 5#64) = some 5) :
    StackSlot.ofWord (rd m a) = .junk := by
  obtain ⟨x6, hx6⟩ := Option.isSome_iff_exists.mp (hm (a + 6#64) (Or.inl (by bv_omega)))
  obtain ⟨x7, hx7⟩ := Option.isSome_iff_exists.mp (hm (a + 7#64) (Or.inl (by bv_omega)))
  have hl : m.loadInt a 8 = some (Int.ofBytes [0, 0, 0, 0, 1, 5, x6, x7]) :=
    loadInt_bytes [0, 0, 0, 0, 1, 5, x6, x7] fun i hi => by
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ => exact h0 _ (by decide)
      | 4, _ => exact h4
      | 5, _ => exact h5
      | 6, _ => exact hx6
      | 7, _ => exact hx7
  have h6 := x6.toNat_lt
  have h7 := x7.toNat_lt
  have hv : Int.ofBytes [0, 0, 0, 0, 1, 5, x6, x7] =
      (((x6.toNat + 256 * x7.toNat) * 2 ^ 48 + 5 * 2 ^ 40 + 2 ^ 32 : Nat) : Int) := by
    simp only [Int.ofBytes, List.foldr_cons, List.foldr_nil, UInt8.reduceToNat]
    omega
  refine ofWord_low (y := x6.toNat + 256 * x7.toNat) ?_
  rw [rd, hl, Option.get!_some, hv, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The precondition as facts for `omega` -/

section
variable {s : MachineData} {A : MachineData → Prop}

-- The bounds and the separations of `Pre`. A separation of two regions is a pair of
-- distances (the form of `region_sep`): `hs1` struct and frame, `hs2` data and frame, `hs3`
-- operations and frame, `hs4` struct and data, `hs5` struct and operations, `hs6` data and
-- operations.
theorem facts (hpre : Pre 8 A s) (hL : (st s).len < (env s).n) (hd : (rdx s).toNat < (env s).n)
    (hN : (st s).trace.length < cap s) :
    (rd s.dmem (s.regs.rdi.toBitVec + 32#64)).toNat < nOf s.dmem s.regs.rdi.toBitVec
    ∧ s.regs.rdx.toBitVec.toNat < nOf s.dmem s.regs.rdi.toBitVec
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 48#64)).toNat < 6 * nOf s.dmem s.regs.rdi.toBitVec
    ∧ nOf s.dmem s.regs.rdi.toBitVec ≤ 1024
    ∧ (16464 ≤ (s.regs.rsp.toBitVec - 8#64 - s.regs.rdi.toBitVec).toNat
      ∧ 8 ≤ (s.regs.rdi.toBitVec - (s.regs.rsp.toBitVec - 8#64)).toNat)
    ∧ (8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rsp.toBitVec - 8#64 - rd s.dmem (s.regs.rdi.toBitVec + 24#64)).toNat
      ∧ 8 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 24#64) - (s.regs.rsp.toBitVec - 8#64)).toNat)
    ∧ (72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rsp.toBitVec - 8#64 - rd s.dmem (s.regs.rdi.toBitVec + 40#64)).toNat
      ∧ 8 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 40#64) - (s.regs.rsp.toBitVec - 8#64)).toNat)
    ∧ (16464 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 24#64) - s.regs.rdi.toBitVec).toNat
      ∧ 8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rdi.toBitVec - rd s.dmem (s.regs.rdi.toBitVec + 24#64)).toNat)
    ∧ (16464 ≤ (rd s.dmem (s.regs.rdi.toBitVec + 40#64) - s.regs.rdi.toBitVec).toNat
      ∧ 72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (s.regs.rdi.toBitVec - rd s.dmem (s.regs.rdi.toBitVec + 40#64)).toNat)
    ∧ (8 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (rd s.dmem (s.regs.rdi.toBitVec + 40#64) - rd s.dmem (s.regs.rdi.toBitVec + 24#64)).toNat
      ∧ 72 * nOf s.dmem s.regs.rdi.toBitVec
        ≤ (rd s.dmem (s.regs.rdi.toBitVec + 24#64) - rd s.dmem (s.regs.rdi.toBitVec + 40#64)).toNat)
    ∧ s.regs.rdi.toBitVec.toNat + 16464 ≤ 2 ^ 64
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 24#64)).toNat + 8 * nOf s.dmem s.regs.rdi.toBitVec ≤ 2 ^ 64
    ∧ (rd s.dmem (s.regs.rdi.toBitVec + 40#64)).toNat + 72 * nOf s.dmem s.regs.rdi.toBitVec
      ≤ 2 ^ 64 := by
  have hw := hpre.1
  have hfr := hpre.2.1
  have hle := hfr.le
  have hsep := hfr.sep_struct (by decide)
  have hst := hw.struct_lt
  have hn : _ ≤ 1024 := hw.n_le
  simp only [cap, st, env, n_envOf, len_stOf, nops_stOf] at hL hd hN
  have hn0 : 0 < nOf s.dmem (rdi s) := by omega
  have hsd := hw.sep_data hn0
  have hso := hw.sep_ops hn0
  have hdo := hw.sep_data_ops hn0
  have hdl := hw.data_lt
  have hol := hw.ops_lt
  have hfd := hfr.sep_data (by decide) hn0
  have hfo := hfr.sep_ops (by decide) hn0
  simp only [WORDS_eq, dataOf, opsOf] at hle hsep hst hsd hso hdo hdl hol hfd hfo
  bbu_norm at hL hd hN hle hsep hst hn hsd hso hdo hdl hol hfd hfo ⊢
  generalize nOf s.dmem s.regs.rdi.toBitVec = n at *
  refine ⟨hL, hd, hN, hn, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hst, hdl,
    hol⟩ <;> bv_omega


-- The word that `cmpq $-1, 8248(%rdi,%rdx,8)` reads is `m_positionOf[d]`.
theorem pos_word {ra : Int64} (hpre : Pre 8 A s) (hL : (st s).len < (env s).n)
    (hd : (rdx s).toNat < (env s).n) (hN : (st s).trace.length < cap s) :
    optOf (rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
      (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec * 8#64 + 8248#64))
      = positionOf (st s) (rdx s).toNat := by
  obtain ⟨-, hd', -, hn, hs1, -⟩ := facts hpre hL hd hN
  clear hpre hL hd hN
  simp only [st, rdi, rdx, Reg64s.get64_rdi, Reg64s.get64_rdx]
  rw [positionOf_stOf hd', wordAt_pos]
  generalize nOf s.dmem s.regs.rdi.toBitVec = n at *
  pd_rd

-- The flag of `cmpq $-1, 8248(%rdi,%rdx,8)` tells if the destination has a slot.
theorem pos_flag {ra : Int64} (hpre : Pre 8 A s) (hL : (st s).len < (env s).n)
    (hd : (rdx s).toNat < (env s).n) (hN : (st s).trace.length < cap s)
    {r : StatusFlags.from_result.Remaining} {b : Bool}
    (h : CondCode.nz.interp (StatusFlags.from_result
      (rd (Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
        (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec * 8#64 + 8248#64) - 18446744073709551615#64)
      r) = b) :
    (positionOf (st s) (rdx s).toNat).isSome = b := by
  rw [← pos_word (ra := ra) hpre hL hd hN, ← h, nz_sub]
  simp only [optOf]
  split <;> simp_all

end

/-! ## The model state after `add` -/

-- The model state after `add`, from the words in memory.
theorem st_add {m m' : Mem 64} {S : Addr} {slot : StackSlot} {d : Nat} {op : Op}
    (hnone : positionOf (stOf m S) d = none) (hn : nOf m' S = nOf m S)
    (hlen : (rd m' (wordAt S 4)).toNat = (rd m (wordAt S 4)).toNat + 1)
    (hpend : rd m' (wordAt S PEND) = rd m (wordAt S PEND))
    (hnops : (rd m' (wordAt S 6)).toNat = (rd m (wordAt S 6)).toNat + 1)
    (hdata : dataOf m' S = dataOf m S)
    (hval : ∀ i < (rd m (wordAt S 4)).toNat,
      rd m' (wordAt (dataOf m S) i) = rd m (wordAt (dataOf m S) i))
    (hvalL : StackSlot.ofWord (rd m' (wordAt (dataOf m S) (rd m (wordAt S 4)).toNat)) = slot)
    (hdest : ∀ i < (rd m (wordAt S 4)).toNat,
      rd m' (wordAt S (DEST + i)) = rd m (wordAt S (DEST + i)))
    (hdestL : (rd m' (wordAt S (DEST + (rd m (wordAt S 4)).toNat))).toNat = d)
    (hpos : ∀ e < nOf m S, e ≠ d → rd m' (wordAt S (POS + e)) = rd m (wordAt S (POS + e)))
    (hposd : optOf (rd m' (wordAt S (POS + d))) = some (rd m (wordAt S 4)).toNat)
    (hop : ∀ i < (rd m (wordAt S 6)).toNat, opOf m' S i = opOf m S i)
    (hopN : opOf m' S (rd m (wordAt S 6)).toNat = op) :
    add (stOf m S) slot d op = .ok (stOf m' S) := by
  rw [add_eq]
  rw [hnone]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Except.ok.injEq]
  symm
  apply stOf_eq
  · simp [St.len, stOf, hlen]
  · simp [stOf, hpend]
  · simp [stOf, hnops]
  · intro i hi
    simp only [St.len, stOf, List.length_append, List.length_map, List.length_range,
      List.length_singleton] at hi
    simp only [stOf]
    rcases Nat.lt_or_ge i (rd m (wordAt S 4)).toNat with h | h
    · rw [List.getElem_append_left (by simpa using h)]
      simp only [List.getElem_map, List.getElem_range, slotOf, hdata, hval i h, hdest i h]
    · have : i = (rd m (wordAt S 4)).toNat := by omega
      subst this
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_singleton, slotOf,
        hdata, hvalL, hdestL]
  · simp [stOf, hn]
  · intro e he
    simp only [stOf, List.length_set, List.length_map, List.length_range] at he
    simp only [stOf, List.getElem_set]
    split
    · subst_vars; rw [hposd]; simp [St.len]
    · simp only [List.getElem_map, List.getElem_range]; rw [hpos e he (Ne.symm ‹_›)]
  · intro i hi
    simp only [stOf, List.length_append, List.length_map, List.length_range,
      List.length_singleton] at hi
    simp only [stOf]
    rcases Nat.lt_or_ge i (rd m (wordAt S 6)).toNat with h | h
    · rw [List.getElem_append_left (by simpa using h)]
      simp only [List.getElem_map, List.getElem_range, hop i h]
    · have : i = (rd m (wordAt S 6)).toNat := by omega
      subst this
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_singleton, hopN]

end PushDup

end Bbu
