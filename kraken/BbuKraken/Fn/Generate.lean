import BbuKraken.Kit
import BbuKraken.ModelLemmas

/-!
The body triple of `generate` (`c/bbu/generate.S`). The body pushes `rbp` and
`rbx` and calls `produce`. It exits with `-2` (`.LB45`) when the target is out of
range. When the two slot values are equal, it swaps the two dests inline; else it
calls `swapWith` (`.LB44`) when the depth is at most 16. The other paths end at `.LB42`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace Generate

-- The registers that `generate` saves, in the order of the pushes.
abbrev regs : List Reg64 := [.rbp, .rbx]

-- The memory of `generate`: the frame of 96 bytes, the saved words and the struct.
abbrev Fm := Kit.Fm 96 regs

section
variable {s : MachineData}

-- The callee-saved registers.
theorem saved_regs {t : MachineData} (hbx : t.regs.rbx.toBitVec = s.regs.rbx.toBitVec)
    (hbp : t.regs.rbp.toBitVec = s.regs.rbp.toBitVec)
    (h12 : t.regs.r12.toBitVec = s.regs.r12.toBitVec) (h13 : t.regs.r13.toBitVec = s.regs.r13.toBitVec)
    (h14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec) (h15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec) :
    ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      t.regs.get64 q = s.regs.get64 q := by
  intro q hq
  cases q <;> simp_all

end

/-! ## The model state in memory -/

section
variable {m : Mem 64} {S : Addr} {k : Nat}

-- A store to the word `k` of the struct keeps the other words.
theorem map_rd (hw : Wf m S) (hk : k < WORDS) {j : Nat} (hj : j < WORDS) (hjk : j ≠ k) (v : Int) :
    rd (m.storeInt (wordAt S k) 8 v) (wordAt S j) = rd m (wordAt S j) := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs hk hj
  exact rd_store_other _ (by simp only [wordAt]; bv_omega)

theorem map_n (hw : Wf m S) (hk1 : DEST ≤ k) (hk : k < WORDS) (v : Int) :
    nOf (m.storeInt (wordAt S k) 8 v) S = nOf m S := by
  unfold nOf; rw [map_rd hw hk (by decide) (by simp only [DEST_eq] at hk1; omega)]

-- A store to the word `k ≥ DEST` of the struct keeps the working stack.
theorem map_data (hw : Wf m S) (hk : k < WORDS) {j : Nat} (hj : j < nOf m S) (v : Int) :
    rd (m.storeInt (wordAt S k) 8 v) (wordAt (dataOf m S) j) = rd m (wordAt (dataOf m S) j) := by
  have hs := hw.struct_lt
  have hd := hw.data_lt
  simp only [WORDS_eq] at hs hk
  refine rd_storeInt_of_disjoint fun x hx hy => hw.disj_struct x ?_ (Or.inl ?_)
  · simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hx ⊢; bv_omega
  · simp only [Mem.Blocks.Inside, or_false] at hy ⊢; bv_omega

-- A store to the word `k ≥ DEST` of the struct keeps the ops buffer.
theorem map_op (hw : Wf m S) (hk1 : DEST ≤ k) (hk : k < WORDS) {i : Nat} (hi : i < 6 * nOf m S)
    (v : Int) : opOf (m.storeInt (wordAt S k) 8 v) S i = opOf m S i := by
  have hs := hw.struct_lt
  have ho := hw.ops_lt
  have hops : opsOf (m.storeInt (wordAt S k) 8 v) S = opsOf m S :=
    map_rd hw hk (j := 6) (by decide) (by simp only [DEST_eq] at hk1; omega) v
  simp only [WORDS_eq] at hs hk
  have hin : ∀ (a : Addr) (n : Nat), (a - (opsOf m S + BitVec.ofNat 64 (12 * i))).toNat + n ≤ 12 →
      Mem.Blocks.Disjoint [(wordAt S k, 8)] [(a, n)] := fun a n hc x hx hy =>
    hw.disj_struct x (by simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hx ⊢; bv_omega)
      (Or.inr (Or.inl (by simp only [Mem.Blocks.Inside, or_false] at hy ⊢; bv_omega)))
  simp only [opOf, opAt, hops]
  rw [rdb_storeInt_of_disjoint (hin _ 1 (by simp)), rdb_storeInt_of_disjoint (hin _ 1 (by bv_omega)),
    rd_storeInt_of_disjoint (hin _ 8 (by bv_omega))]

-- A store to the word `k ≥ DEST` of the struct keeps it well formed.
theorem wf_store_map (hw : Wf m S) (hk1 : DEST ≤ k) (hk : k < WORDS) (v : Int) :
    Wf (m.storeInt (wordAt S k) 8 v) S := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs hk
  have hu : Mem.UnchangedOutside [(wordAt S k, 8)] m (m.storeInt (wordAt S k) 8 v) :=
    Mem.UnchangedOutside.storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  refine Wf.congr hu hw ?_ (fun x hx => (hw.mapped.storeInt _ _ _) x (inside_append.mpr (Or.inl hx)))
    ?_ ?_
  · intro x hr hx
    simp only [Mem.Blocks.Inside, or_false] at hx
    rcases hr with hr | hr
    · simp only [wordAt, DEST_eq] at hr hx hk1; bv_omega
    · exact hw.disj_struct x (Or.inl (by simp only [wordAt, WORDS_eq] at hx ⊢; bv_omega))
        (Or.inr (Or.inr (Or.inr hr)))
  · rw [map_rd hw (by simp only [WORDS_eq]; exact hk) (j := 0) (by decide)
      (by simp only [DEST_eq] at hk1; omega)]
    exact hw.len_le
  · rw [map_rd hw (by simp only [WORDS_eq]; exact hk) (j := 2) (by decide)
      (by simp only [DEST_eq] at hk1; omega)]
    exact hw.nops_le

end

section
variable {m : Mem 64} {S : Addr}

-- `stOf_eq` with the fields of the state.
theorem stOf_eq' {sl : List Slot} {pos : List (Option Nat)} {p : Nat} {ops : List Op}
    (hlen : (rd m (wordAt S 0)).toNat = sl.length) (hpend : (rd m (wordAt S 1)).toNat = p)
    (hnops : (rd m (wordAt S 2)).toNat = ops.length)
    (hslot : ∀ i (hi : i < sl.length), slotOf m S i = sl[i]) (hplen : pos.length = nOf m S)
    (hpos : ∀ d (hd : d < pos.length), optOf (rd m (wordAt S (POS + d))) = pos[d])
    (hop : ∀ i (hi : i < ops.length), opOf m S i = ops[i]) : stOf m S = ⟨sl, pos, p, ops⟩ :=
  stOf_eq hlen hpend hnops hslot hplen hpos hop

-- A store to the dest word `i` sets the dest of slot `i`.
theorem stOf_store_dest (hw : Wf m S) {i : Nat} (hi : i < (stOf m S).len) (x : Word) :
    stOf (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) S =
      { stOf m S with slots := (stOf m S).slots.set i ⟨(stOf m S).val i, x.toNat⟩ } := by
  have hl := hw.len_le
  have hn := hw.n_le
  rw [len_stOf] at hi
  have hk : DEST + i < WORDS := by simp only [DEST_eq, WORDS_eq, MAX_N] at hn ⊢; omega
  have hr : ∀ j, j < WORDS → j ≠ DEST + i →
      rd (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) (wordAt S j) = rd m (wordAt S j) :=
    fun j hj hji => map_rd hw hk hj hji _
  have hdata : dataOf (m.storeInt (wordAt S (DEST + i)) 8 x.toInt) S = dataOf m S :=
    hr 8 (by decide) (by simp only [DEST_eq]; omega)
  have hnn := map_n hw (Nat.le_add_right _ _) hk x.toInt
  apply stOf_eq'
  · rw [hr 0 (by decide) (by simp only [DEST_eq]; omega)]; simp [stOf]
  · rw [hr 1 (by decide) (by simp only [DEST_eq]; omega)]; simp [stOf]
  · rw [hr 2 (by decide) (by simp only [DEST_eq]; omega)]; simp [stOf]
  · intro j hj
    have hj' : j < (rd m (wordAt S 0)).toNat := by simpa [St.len, stOf] using hj
    simp only [slotOf, hdata, map_data hw hk (j := j) (by omega)]
    by_cases hji : i = j
    · subst hji
      simp only [List.getElem_set_self]
      rw [rd_store_same _ rfl, BitVec.ofInt_toInt, val_stOf hi]
    · simp only [List.getElem_set_ne hji]
      rw [hr (DEST + j) (by simp only [DEST_eq, WORDS_eq, MAX_N] at hn ⊢; omega) (by omega)]
      simp [stOf, slotOf]
  · simp [stOf, hnn]
  · intro d hd
    simp only [stOf, List.length_map, List.length_range] at hd
    rw [hr (POS + d) (by simp only [POS_eq, WORDS_eq, MAX_N] at hn ⊢; omega)
      (by simp only [POS_eq, DEST_eq, MAX_N] at hn ⊢; omega)]
    simp [stOf]
  · intro j hj
    have := hw.nops_le
    simp only [stOf, List.length_map, List.length_range] at hj
    rw [map_op hw (Nat.le_add_right _ _) hk (by omega)]
    simp [stOf]

-- A store to the position word `d` sets `positionOf d`.
theorem stOf_store_pos (hw : Wf m S) {d : Nat} (hd : d < nOf m S) (x : Word) :
    stOf (m.storeInt (wordAt S (POS + d)) 8 x.toInt) S =
      { stOf m S with positionOf := (stOf m S).positionOf.set d (optOf x) } := by
  have hl := hw.len_le
  have hn := hw.n_le
  have hk : POS + d < WORDS := by simp only [POS_eq, WORDS_eq, MAX_N] at hn ⊢; omega
  have hk1 : DEST ≤ POS + d := by simp only [POS_eq, DEST_eq]; omega
  have hr : ∀ j, j < WORDS → j ≠ POS + d →
      rd (m.storeInt (wordAt S (POS + d)) 8 x.toInt) (wordAt S j) = rd m (wordAt S j) :=
    fun j hj hji => map_rd hw hk hj hji _
  have hdata : dataOf (m.storeInt (wordAt S (POS + d)) 8 x.toInt) S = dataOf m S :=
    hr 8 (by decide) (by simp only [POS_eq]; omega)
  have hnn := map_n hw hk1 hk x.toInt
  apply stOf_eq'
  · rw [hr 0 (by decide) (by simp only [POS_eq]; omega)]; simp [stOf]
  · rw [hr 1 (by decide) (by simp only [POS_eq]; omega)]; simp [stOf]
  · rw [hr 2 (by decide) (by simp only [POS_eq]; omega)]; simp [stOf]
  · intro j hj
    simp only [stOf, List.length_map, List.length_range] at hj
    simp only [slotOf, hdata, map_data hw hk (j := j) (by omega)]
    rw [hr (DEST + j) (by simp only [DEST_eq, WORDS_eq, MAX_N] at hn ⊢; omega)
      (by simp only [POS_eq, DEST_eq, MAX_N] at hn ⊢; omega)]
    simp [stOf, slotOf]
  · simp [stOf, hnn]
  · intro j hj
    simp only [stOf, List.length_set, List.length_map, List.length_range] at hj
    rw [List.getElem_set]
    split
    · subst_vars
      rw [rd_store_same _ rfl, BitVec.ofInt_toInt]
    · rw [hr (POS + j) (by simp only [POS_eq, WORDS_eq, MAX_N] at hn ⊢; omega) (by omega)]
      simp [stOf]
  · intro j hj
    have := hw.nops_le
    simp only [stOf, List.length_map, List.length_range] at hj
    rw [map_op hw hk1 hk (by omega)]
    simp [stOf]

end

/-! ## The swap of the equal branch -/

theorem addr_dest (S y : Word) : S + y * 8#64 + 72#64 = wordAt S (DEST + y.toNat) := by
  simp only [wordAt, DEST_eq]; bv_omega

theorem addr_pos (S y : Word) : S + y * 8#64 + 8264#64 = wordAt S (POS + y.toNat) := by
  simp only [wordAt, POS_eq]; bv_omega

theorem addr_data (D y : Word) : D + y * 8#64 = wordAt D y.toNat := by
  simp only [wordAt]; bv_omega

-- The four stores of the equal branch: the dest words of slot `x` and of the top
-- slot swap, and the position words of the two dests point to the slots.
def swap4 (m : Mem 64) (S x : Word) : Mem 64 :=
  let A := S + x * 8#64 + 72#64
  let B := S + (rd m S + -1#64) * 8#64 + 72#64
  let m2 := (m.storeInt A 8 (rd m B).toInt).storeInt B 8 (rd m A).toInt
  (m2.storeInt (S + rd m2 A * 8#64 + 8264#64) 8 x.toInt).storeInt (S + rd m A * 8#64 + 8264#64) 8
    (rd m S + -1#64).toInt

-- The struct at `S` holds `st1`, and slot `x` is below the top slot.
structure Sw (m : Mem 64) (S x : Word) (st1 : St) : Prop where
  wf : Wf m S
  st : stOf m S = st1
  pos : Pos (nOf m S) st1
  lt : x.toNat + 1 < st1.len

section
variable {m : Mem 64} {S x : Word} {st1 : St}

theorem Sw.len (h : Sw m S x st1) : (rd m S).toNat = st1.len := by
  rw [← h.st, len_stOf]; simp [wordAt]

theorem Sw.top (h : Sw m S x st1) : (rd m S + -1#64).toNat = st1.len - 1 := by
  have := h.len; have := h.lt; bv_omega

theorem Sw.len_le (h : Sw m S x st1) : st1.len ≤ 1024 := by
  have := h.wf.len_le; have := h.wf.n_le; rw [← h.len]; simp only [MAX_N] at *; simp_all [wordAt]; omega

-- The dest of slot `i` and its bound.
theorem Sw.dest (h : Sw m S x st1) {i : Nat} (hi : i < st1.len) :
    (rd m (wordAt S (DEST + i))).toNat = st1.dest i ∧ st1.dest i < nOf m S := by
  refine ⟨?_, ?_⟩
  · rw [← h.st, dest_stOf (by rw [← h.st, len_stOf] at hi; exact hi)]
  · have hd := h.pos.dests.1 i (by rw [St.length_dests]; exact hi)
    rwa [St.dest_eq, getElem!_pos st1.dests i (by rw [St.length_dests]; exact hi)]

theorem optOf_lt {w : Word} (h : w.toNat < 1024) : optOf w = some w.toNat := by
  unfold optOf; rw [ite_eq_right_iff.mpr (fun he => by subst he; simp at h)]

-- The four stores swap the dests of slot `x` and of the top slot.
theorem Sw.swap (h : Sw m S x st1) :
    stOf (swap4 m S x) S = swapDestinations st1 x.toNat (st1.len - 1) := by
  have hl := h.len_le
  have hlt := h.lt
  have hn := h.wf.n_le
  simp only [MAX_N] at hn
  have ha : x.toNat < st1.len := by omega
  have hb : st1.len - 1 < st1.len := by omega
  obtain ⟨hda, hdan⟩ := h.dest ha
  obtain ⟨hdb, hdbn⟩ := h.dest hb
  have hka : DEST + x.toNat < WORDS := by simp only [DEST_eq, WORDS_eq]; omega
  have hkb : DEST + (st1.len - 1) < WORDS := by simp only [DEST_eq, WORDS_eq]; omega
  unfold swap4
  simp only [addr_dest, addr_pos, h.top]
  generalize hv1 : rd m (wordAt S (DEST + (st1.len - 1))) = v1 at hdb
  generalize hv2 : rd m (wordAt S (DEST + x.toNat)) = v2 at hda
  have hw1 := wf_store_map h.wf (Nat.le_add_right _ _) hka v1.toInt
  have hw2 := wf_store_map hw1 (Nat.le_add_right _ _) hkb v2.toInt
  rw [map_rd hw1 hkb hka (by omega), rd_store_same _ rfl, BitVec.ofInt_toInt]
  have hk3 : POS + v1.toNat < WORDS := by simp only [POS_eq, WORDS_eq]; omega
  have hw3 := wf_store_map hw2 (by simp only [POS_eq, DEST_eq]; omega) hk3 x.toInt
  have hn1 := map_n h.wf (Nat.le_add_right _ _) hka v1.toInt
  have hn2 := map_n hw1 (Nat.le_add_right _ _) hkb v2.toInt
  have hn3 := map_n hw2 (by simp only [POS_eq, DEST_eq]; omega) hk3 x.toInt
  rw [stOf_store_pos hw3 (by omega), stOf_store_pos hw2 (by omega),
    stOf_store_dest hw1 (by rw [stOf_store_dest h.wf (by rw [h.st]; exact ha)]; simpa [St.len, h.st] using hb),
    stOf_store_dest h.wf (by rw [h.st]; exact ha), h.st, hda, hdb]
  rw [optOf_lt (by omega), optOf_lt (by rw [h.top]; omega), h.top]
  have hab : x.toNat ≠ st1.len - 1 := by omega
  have ha' : x.toNat < st1.slots.length := ha
  have hb' : st1.len - 1 < st1.slots.length := hb
  simp [swapDestinations, St.val, St.dest, hab, Ne.symm hab, ha', hb']


-- The dest words of slot `x` and of the top slot.
theorem Sw.dest_a (h : Sw m S x st1) : (rd m (S + x * 8#64 + 72#64)).toNat < nOf m S := by
  rw [addr_dest]; have := h.dest (i := x.toNat) (by have := h.lt; omega); omega

theorem Sw.dest_b (h : Sw m S x st1) :
    (rd m (S + (rd m S + -1#64) * 8#64 + 72#64)).toNat < nOf m S := by
  rw [addr_dest, h.top]; have := h.dest (i := st1.len - 1) (by have := h.lt; omega); omega

theorem Sw.ld_a (h : Sw m S x st1) : (m.loadInt (S + x * 8#64 + 72#64) 8).isSome = true := by
  have := h.len_le; have := h.lt
  rw [addr_dest]; exact h.wf.word_isSome h.wf.mapped (by simp only [DEST_eq, WORDS_eq]; omega)

theorem Sw.ld_b (h : Sw m S x st1) :
    (m.loadInt (S + (rd m S + -1#64) * 8#64 + 72#64) 8).isSome = true := by
  have := h.len_le; have := h.lt
  rw [addr_dest, h.top]; exact h.wf.word_isSome h.wf.mapped (by simp only [DEST_eq, WORDS_eq]; omega)

theorem Sw.ld_pos (h : Sw m S x st1) {y : Word} (hy : y.toNat < nOf m S) :
    (m.loadInt (S + y * 8#64 + 8264#64) 8).isSome = true := by
  have := h.wf.n_le; simp only [MAX_N] at this
  rw [addr_pos]; exact h.wf.word_isSome h.wf.mapped (by simp only [POS_eq, WORDS_eq]; omega)

-- After the two dest stores, the dest word of slot `x` holds the old top dest.
theorem Sw.rd2 (h : Sw m S x st1) :
    rd ((m.storeInt (S + x * 8#64 + 72#64) 8 (rd m (S + (rd m S + -1#64) * 8#64 + 72#64)).toInt).storeInt
      (S + (rd m S + -1#64) * 8#64 + 72#64) 8 (rd m (S + x * 8#64 + 72#64)).toInt) (S + x * 8#64 + 72#64)
      = rd m (S + (rd m S + -1#64) * 8#64 + 72#64) := by
  have := h.len_le; have := h.lt
  have hka : DEST + x.toNat < WORDS := by simp only [DEST_eq, WORDS_eq]; omega
  have hkb : DEST + (st1.len - 1) < WORDS := by simp only [DEST_eq, WORDS_eq]; omega
  simp only [addr_dest, h.top]
  rw [map_rd (wf_store_map h.wf (Nat.le_add_right _ _) hka _) hkb hka (by omega), rd_store_same _ rfl,
    BitVec.ofInt_toInt]

-- The words of the working stack.
theorem Sw.ld_val (h : Sw m S x st1) : (m.loadInt (rd m (S + 64#64) + x * 8#64) 8).isSome = true := by
  have hd := h.wf.data_lt
  have hl := h.wf.len_le
  have hn := h.wf.n_le
  have := h.lt
  rw [len_stOf.symm.trans (congrArg St.len h.st)] at hl
  simp only [MAX_N] at hn
  refine Mem.Mapped.loadInt_isSome (fun y hy => h.wf.mapped y (inside_append.mpr (Or.inl hy)))
    (inside_writable (Or.inr (Or.inr (Or.inl ?_))))
  rw [show rd m (S + 64#64) = dataOf m S from rfl]; bv_omega

theorem Sw.ld_top (h : Sw m S x st1) :
    (m.loadInt (rd m (S + 64#64) + (rd m S + -1#64) * 8#64) 8).isSome = true := by
  have hd := h.wf.data_lt
  have hl := h.wf.len_le
  have hn := h.wf.n_le
  have := h.lt
  have ht := h.top
  rw [len_stOf.symm.trans (congrArg St.len h.st)] at hl
  simp only [MAX_N] at hn
  refine Mem.Mapped.loadInt_isSome (fun y hy => h.wf.mapped y (inside_append.mpr (Or.inl hy)))
    (inside_writable (Or.inr (Or.inr (Or.inl ?_))))
  rw [show rd m (S + 64#64) = dataOf m S from rfl]; bv_omega

-- `(a ^ b) << 16 == 0`: the values of slot `x` and of the top slot are equal.
theorem Sw.val (h : Sw m S x st1) :
    (rd m (rd m (S + 64#64) + x * 8#64) ^^^ rd m (rd m (S + 64#64) + (rd m S + -1#64) * 8#64)) <<< 16
      = 0#64 ↔ st1.val x.toNat = st1.val (st1.len - 1) := by
  have := h.lt
  have hl : (rd m (wordAt S 0)).toNat = st1.len := by rw [← h.st, len_stOf]
  have e1 : st1.val x.toNat = StackSlot.ofWord (rd m (wordAt (dataOf m S) x.toNat)) := by
    have := val_stOf (m := m) (S := S) (i := x.toNat) (by omega : _ < (rd m (wordAt S 0)).toNat); rwa [h.st] at this
  have e2 : st1.val (st1.len - 1) = StackSlot.ofWord (rd m (wordAt (dataOf m S) (st1.len - 1))) := by
    have := val_stOf (m := m) (S := S) (i := st1.len - 1) (by omega : _ < (rd m (wordAt S 0)).toNat); rwa [h.st] at this
  rw [← ofWord_eq_iff, show rd m (S + 64#64) = dataOf m S from rfl, addr_data, addr_data, h.top, e1, e2]

end
/-! ## The frame of `generate` -/

section
variable {s : MachineData} {ra : Int64}

theorem fm_isSome {m : Mem 64} (h : Fm s ra m) {a : Addr}
    (ha : (a - (s.regs.rsp.toBitVec - 96#64)).toNat + 8 ≤ 96) : (m.loadInt a 8).isSome = true :=
  h.map.loadInt_isSome (Or.inl ha)

-- A store to the word `k ≥ DEST` of the struct keeps the frame.
theorem Fm.store_map {A : MachineData → Prop} {m : Mem 64} (hpre : Pre 96 A s) (h : Fm s ra m)
    {k : Nat} (hk1 : DEST ≤ k) (hk : k < WORDS) (v : Int) :
    Fm s ra (m.storeInt (wordAt (rdi s) k) 8 v) := by
  have hs := h.wf.struct_lt
  have hwr := (h.keeps hpre).2.2
  have hn := h.n hpre
  have hk0 : 0 ≠ k := by simp only [DEST_eq] at hk1; omega
  have hk2 : 2 ≠ k := by simp only [DEST_eq] at hk1; omega
  have hw : Mem.Blocks.Inside (wordAt (rdi s) k) 8 (writable s.dmem (rdi s)) := by
    simp only [WORDS_eq, DEST_eq] at hs hk hk1
    exact inside_writable (Or.inr (Or.inl (by simp only [wordAt, DEST_eq, WORDS_eq]; bv_omega)))
  refine Kit.Fm.write (by decide) hpre h (.storeInt (fun _ _ => rfl) hw _) ?_ ?_ ?_
  · rw [← hwr]
    exact Mem.Mapped.storeInt (fun x hx => h.wf.mapped x (inside_append.mpr (Or.inl hx))) _ _ _
  · rw [map_rd h.wf hk (by decide) hk0, ← hn]; exact h.wf.len_le
  · rw [map_rd h.wf hk (by decide) hk2, ← hn]; exact h.wf.nops_le

-- The four stores of the equal branch keep the frame.
theorem Fm.swap {A : MachineData → Prop} {m : Mem 64} {x : Word} {st1 : St} (hpre : Pre 96 A s)
    (h : Fm s ra m) (hs : Sw m (rdi s) x st1) : Fm s ra (swap4 m (rdi s) x) := by
  have hl := hs.len_le
  have hlt := hs.lt
  have hn := h.wf.n_le
  simp only [MAX_N] at hn
  obtain ⟨hda, hdan⟩ := hs.dest (i := x.toNat) (by omega)
  obtain ⟨hdb, hdbn⟩ := hs.dest (i := st1.len - 1) (by omega)
  have hka : DEST + x.toNat < WORDS := by simp only [DEST_eq, WORDS_eq]; omega
  have hkb : DEST + (st1.len - 1) < WORDS := by simp only [DEST_eq, WORDS_eq]; omega
  unfold swap4
  simp only [addr_dest, addr_pos, hs.top]
  generalize hv1 : rd m (wordAt (rdi s) (DEST + (st1.len - 1))) = v1 at hdb
  have hw1 := wf_store_map hs.wf (Nat.le_add_right _ _) hka v1.toInt
  rw [map_rd hw1 hkb hka (by omega), rd_store_same _ rfl, BitVec.ofInt_toInt]
  have h1 := h.store_map hpre (Nat.le_add_right _ _) hka v1.toInt
  have h2 := h1.store_map hpre (Nat.le_add_right _ _) hkb (rd m (wordAt (rdi s) (DEST + x.toNat))).toInt
  have h3 := h2.store_map hpre (k := POS + v1.toNat) (by simp only [POS_eq, DEST_eq]; omega)
    (by simp only [POS_eq, WORDS_eq]; omega) x.toInt
  exact h3.store_map hpre (k := POS + (rd m (wordAt (rdi s) (DEST + x.toNat))).toNat)
    (by simp only [POS_eq, DEST_eq]; omega) (by simp only [POS_eq, WORDS_eq]; omega) _


end
/-! ## The calls -/

theorem ok_congr {α : Type} {c s t : MachineData} {enc : α → Word} {f : α → St}
    (h : rdi c = rdi s) : Ok c t enc f = Ok s t enc f := by
  unfold Ok st'; rw [h]

-- The registers of `generate` after the pushes.
structure Rg (s t : MachineData) : Prop where
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 24#64
  bp : t.regs.rbp.toBitVec = s.regs.rdi.toBitVec
  bx : t.regs.rbx.toBitVec = s.regs.rsi.toBitVec
  r12 : t.regs.r12.toBitVec = s.regs.r12.toBitVec
  r13 : t.regs.r13.toBitVec = s.regs.r13.toBitVec
  r14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec

section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop}

-- A callee keeps the registers of `Rg`.
theorem Rg.call {c t : MachineData} {G : Nat} (h : Rg s c) (hag : (mod G c).Agree c t) : Rg s t := by
  have hr : ∀ q, q ∉ (mod G c).regs → (t.regs.get64 q) = c.regs.get64 q := hag.1
  have h1 := hr .rsp (by simp [mod])
  have h2 := hr .rbp (by simp [mod])
  have h3 := hr .rbx (by simp [mod])
  have h4 := hr .r12 (by simp [mod])
  have h5 := hr .r13 (by simp [mod])
  have h6 := hr .r14 (by simp [mod])
  have h7 := hr .r15 (by simp [mod])
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_rbx, Reg64s.get64_r12,
    Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1 ▸ h.sp, h2 ▸ h.bp, h3 ▸ h.bx, h4 ▸ h.r12, h5 ▸ h.r13, h6 ▸ h.r14, h7 ▸ h.r15⟩

theorem Rg.rsp {t : MachineData} (h : Rg s t) : rsp t = rsp s - 24#64 := by
  simp only [Reg64s.get64_rsp, h.sp]

theorem Rg.rdi {c : MachineData} (h : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp) : rdi c = rdi s := by
  simp only [Reg64s.get64_rdi, hrdi, h.bp]

-- The precondition of `produce` at the call of the entry block.
theorem produce_pre {c : MachineData} (hpre : Pre 96 generateA s)
    (hc : c.dmem = Kit.pushes s ra regs) (hrg : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp)
    (hrsi : c.regs.rsi = c.regs.rbx) (hd : (rsi s).toNat < (env s).n) : Pre produceF produceA c := by
  have hfm : Fm s ra _ := Kit.Fm.init (by decide) hpre
  have hst := Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre
  have henv := (hfm.keeps hpre).1
  have hrd := hrg.rdi hrdi
  have hA := hpre.2.2
  refine Kit.Fm.pre (k := 24) (by decide) hpre hfm hc hrg.rsp hrd ⟨?_, ?_, ?_⟩
  all_goals simp only [st, env, cap, rsi, Reg64s.get64_rsi, hrsi, hrg.bx, hrd, hc, hst, henv]
  · exact hd
  · exact hA.2.1
  · rw [← n_envOf, henv, n_envOf]; simp only [generateA, st, cap] at hA; omega

-- The state after the call of `produce`.
theorem after_produce {c t : MachineData} (hp : Post produceF produceR c t)
    (hag : (mod produceF c).Agree c t) (hpre : Pre 96 generateA s)
    (hc : c.dmem = Kit.pushes s ra regs) (hrg : Rg s c) (hrdi : c.regs.rdi = c.regs.rbp)
    (hrsi : c.regs.rsi = c.regs.rbx) :
    Fm s ra t.dmem ∧ Rg s t
      ∧ Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t := by
  have hfm : Fm s ra _ := Kit.Fm.init (by decide) hpre
  have hrd := hrg.rdi hrdi
  refine ⟨Kit.Fm.call (k := 24) (by decide) (by decide) hpre hfm hc hrg.rsp hrd hp hag,
    hrg.call hag, ?_⟩
  have h := hp.2.2
  unfold produceR at h
  rw [ok_congr hrd] at h
  simp only [st, env, rsi, Reg64s.get64_rsi, hrsi, hrg.bx, hrd, hc,
    Kit.st_pushes (rs := regs) (ra := ra) (by decide) hpre, (hfm.keeps hpre).1] at h
  exact h

end

/-! ## The model of `generate` -/

section
variable {e : Env} {st st1 : St} {d : Nat}

theorem gen_err {x : Err} (hd : d < e.n) (h : produce e st d = .error x) :
    generate e st d = .error x := by
  unfold generate; simp only [show ¬ e.n ≤ d from by omega, ↓reduceIte, h]; rfl

theorem gen_ok (hd : d < e.n) (h : produce e st d = .ok st1) :
    generate e st d =
      if d + 1 < st1.len ∧ st1.dest d ≠ d then
        if st1.val d = st1.val (st1.len - 1) then .ok (swapDestinations st1 d (st1.len - 1))
        else if st1.len - 1 - d ≤ MAX_SWAP_DEPTH then swapWith st1 d else .ok st1
      else .ok st1 := by
  unfold generate; simp only [show ¬ e.n ≤ d from by omega, ↓reduceIte, h]; rfl

end

/-! ## Results and loads -/

-- `Res` only reads `rax` and the memory.
theorem res_ok {α : Type} {S : Addr} {r : M α} {enc : α → Word} {f : α → St} {s t u : MachineData}
    (h : Res S r (Ok s t enc f) t) (hm : u.dmem = t.dmem) (hax : rax u = rax t) :
    Res S r (Ok s u enc f) u := by
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by rw [st', hm]; exact h.2⟩

-- The words of the struct are mapped.
theorem word_isSome {m : Mem 64} {S a : Addr} (hw : Wf m S) {k : Nat} (hk : k < WORDS)
    (ha : a = wordAt S k) : (m.loadInt a 8).isSome = true :=
  ha ▸ hw.word_isSome hw.mapped hk

/-! ## The entry block -/

section
variable {s : MachineData} {ra : Int64} {A : MachineData → Prop}

-- The word `n` after the push of the return address.
theorem e_n (hpre : Pre 96 A s) :
    (rd (s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt)
      (s.regs.rdi.toBitVec + 24#64)).toNat = (env s).n := by
  have h := hdr_congr (Kit.Mid.init (F := 96) (ra := ra) (by decide) hpre).un hpre.disj (k := 3)
    (by omega) (by omega)
  simp only [MachineData.dmem_pushRa, wordAt, rdi, Reg64s.get64_rdi, Reg64s.get64_rsp] at h
  rw [show s.regs.rdi.toBitVec + 24#64 = s.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * 3) from rfl, h,
    n_envOf]
  rfl

theorem e_ld3 (hpre : Pre 96 A s) :
    ((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      (s.regs.rdi.toBitVec + 24#64) 8).isSome = true :=
  loadInt_isSome_store _ (word_isSome hpre.1 (k := 3) (by decide) rfl)

theorem e_ld16 (hpre : Pre 96 A s) :
    ((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).loadInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact (Kit.Mid.init (F := 96) (ra := ra) (by decide) hpre).map.loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

theorem e_ld24 (hpre : Pre 96 A s) :
    (((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).loadInt
      (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact ((Kit.Mid.init (F := 96) (ra := ra) (by decide) hpre).map.storeInt _ _ _).loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

theorem e_ld32 (hpre : Pre 96 A s) :
    ((Kit.pushes s ra regs).loadInt (s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome
      = true := by
  have hle := hpre.2.1.le
  simp only [rsp, Reg64s.get64_rsp] at hle
  exact (Kit.Fm.init (rs := regs) (ra := ra) (by decide) hpre).map.loadInt_isSome
    (Or.inl (by simp only [rsp, Reg64s.get64_rsp]; bv_omega))

-- The registers at the call of `produce`.
theorem e_rg {c : MachineData} (h1 : c.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64)
    (h2 : c.regs.rbp.toBitVec = s.regs.rdi.toBitVec) (h3 : c.regs.rbx.toBitVec = s.regs.rsi.toBitVec)
    (h4 : c.regs.r12 = s.regs.r12) (h5 : c.regs.r13 = s.regs.r13) (h6 : c.regs.r14 = s.regs.r14)
    (h7 : c.regs.r15 = s.regs.r15) : Rg s c :=
  ⟨by rw [h1]; bv_omega, h2, h3, by rw [h4], by rw [h5], by rw [h6], by rw [h7]⟩

end

/-! ## The invariants -/

section
variable (s : MachineData) (ra : Int64)

-- `.LB45`: `d` is out of range.
def At45 (t : MachineData) : Prop :=
  t.regs = (s.pushRa ra).regs ∧ t.dmem = (s.pushRa ra).dmem ∧ (env s).n ≤ (rsi s).toNat

-- `.LB42`: the result is in `rax` and memory.
def At42 (t : MachineData) : Prop := Fm s ra t.dmem ∧ Rg s t ∧ generateR s t

-- The variant: the back edges from `.LB44` go to `.LB42`.
def V : Label → MachineData → Nat
  | "generate", _ => 2
  | ".LB44", _ => 1
  | _, _ => 0

end

/-! ## After `produce` -/

theorem toNat_add_one (x : Word) (h : x.toNat < 1024) : (x + 1#64).toNat = x.toNat + 1 := by
  bv_omega

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {st1 : St} {A : MachineData → Prop}

theorem Rg.same (h : Rg s t) (h1 : u.regs.rsp = t.regs.rsp) (h2 : u.regs.rbp = t.regs.rbp)
    (h3 : u.regs.rbx = t.regs.rbx) (h4 : u.regs.r12 = t.regs.r12) (h5 : u.regs.r13 = t.regs.r13)
    (h6 : u.regs.r14 = t.regs.r14) (h7 : u.regs.r15 = t.regs.r15) : Rg s u :=
  ⟨h1 ▸ h.sp, h2 ▸ h.bp, h3 ▸ h.bx, h4 ▸ h.r12, h5 ▸ h.r13, h6 ▸ h.r14, h7 ▸ h.r15⟩

-- The stack of a jump target with the registers `Rg`.
theorem Rg.stk (h : Rg s u) :
    ((s.pushRa ra).regs.get64 .rsp - u.regs.get64 .rsp).toNat < 2 ^ 63 := by
  simp only [Reg64s.get64_rsp, pushRa_rsp, h.sp]; bv_omega

-- The state after `produce` returns `ok st1`.
structure Ap (s : MachineData) (ra : Int64) (t : MachineData) (st1 : St) : Prop where
  fm : Fm s ra t.dmem
  rg : Rg s t
  hd : (rsi s).toNat < (env s).n
  hp : produce (env s) (st s) (rsi s).toNat = .ok st1
  hst : st' s t = st1
  ax : t.regs.rax.toBitVec = 0#64

-- `.LB44`: `produce` returns `ok st1`, slot `d` lies below the top slot, its dest is not
-- `d`, and the values of slot `d` and of the top slot differ. `rdx` holds `len`.
def At44 (s : MachineData) (ra : Int64) (t : MachineData) : Prop :=
  ∃ st1, Ap s ra t st1 ∧ (rsi s).toNat + 1 < st1.len ∧ st1.dest (rsi s).toNat ≠ (rsi s).toNat
    ∧ st1.val (rsi s).toNat ≠ st1.val (st1.len - 1)
    ∧ t.regs.rdx.toBitVec = rd t.dmem t.regs.rbp.toBitVec

-- `jne` jumps: `produce` fails.
theorem jne_taken (hd : (rsi s).toNat < (env s).n)
    (h : Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t)
    (hz : t.regs.rax.toBitVec ≠ 0#64) : generateR s t := by
  unfold generateR
  rcases hp : produce (env s) (st s) (rsi s).toNat with (⟨p, x⟩ | _) | st1
  · rw [gen_err hd hp]; rw [hp] at h; exact h
  · rw [gen_err hd hp]; rw [hp] at h; exact h
  · rw [hp] at h
    exact absurd h.1 hz

-- `jne` does not jump: `produce` returns `ok`.
theorem jne_not (hfm : Fm s ra t.dmem) (hrg : Rg s t) (hd : (rsi s).toNat < (env s).n)
    (h : Res (rdi s) (produce (env s) (st s) (rsi s).toNat) (Ok s t (fun _ => 0#64) id) t)
    (hz : t.regs.rax.toBitVec = 0#64) : ∃ st1, Ap s ra t st1 := by
  rcases hp : produce (env s) (st s) (rsi s).toNat with (⟨p, x⟩ | _) | st1
  · rw [hp] at h
    have := h.1
    simp only [rax, Reg64s.get64_rax] at this
    rw [this] at hz
    exact absurd hz (by decide)
  · rw [hp] at h
    simp only [Res, rax, Reg64s.get64_rax] at h
    rw [h] at hz
    exact absurd hz (by decide)
  · rw [hp] at h
    exact ⟨st1, hfm, hrg, hd, hp, h.2, hz⟩

theorem Ap.bp (h : Ap s ra t st1) : t.regs.rbp.toBitVec = rdi s := by
  simp only [rdi, Reg64s.get64_rdi, h.rg.bp]

theorem Ap.bx (h : Ap s ra t st1) : t.regs.rbx.toBitVec = rsi s := by
  simp only [rsi, Reg64s.get64_rsi, h.rg.bx]

theorem Ap.len (h : Ap s ra t st1) : (rd t.dmem t.regs.rbp.toBitVec).toNat = st1.len := by
  rw [← h.hst, st', len_stOf, h.bp]; simp [wordAt]

theorem Ap.len_le (h : Ap s ra t st1) : st1.len ≤ 1024 := by
  have h1 := h.fm.wf.len_le
  have h2 := h.fm.wf.n_le
  simp only [MAX_N] at h2
  rw [← h.hst, st', len_stOf]; omega

theorem Ap.d_lt (hpre : Pre 96 A s) (h : Ap s ra t st1) : (rsi s).toNat < 1024 := by
  have h1 : (env s).n = nOf s.dmem (rdi s) := n_envOf
  have : _ ≤ 1024 := hpre.1.n_le
  have := h.hd
  omega

theorem Ap.lt (hpre : Pre 96 A s) (h : Ap s ra t st1)
    (hc : (t.regs.rbx.toBitVec + 1#64).toNat < (rd t.dmem t.regs.rbp.toBitVec).toNat) :
    (rsi s).toNat + 1 < st1.len := by
  have hd := h.d_lt hpre
  rw [h.len, h.bx, toNat_add_one _ hd] at hc
  omega

theorem Ap.ld0 (h : Ap s ra t st1) : (t.dmem.loadInt t.regs.rbp.toBitVec 8).isSome = true :=
  word_isSome h.fm.wf (k := 0) (by decide) (by rw [h.bp]; simp [wordAt])

theorem Ap.ld8 (h : Ap s ra t st1) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + 64#64) 8).isSome = true :=
  word_isSome h.fm.wf (k := 8) (by decide) (by rw [h.bp])

theorem Ap.ld_dest (hpre : Pre 96 A s) (h : Ap s ra t st1) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 72#64) 8).isSome = true := by
  have hd := h.d_lt hpre
  exact word_isSome h.fm.wf (k := DEST + (rsi s).toNat) (by simp only [DEST_eq, WORDS_eq]; omega)
    (by rw [h.bp, h.bx]; exact addr_dest _ _)

theorem Ap.dest (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len) :
    (rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 72#64)).toNat =
      st1.dest (rsi s).toNat := by
  rw [← h.hst] at hi ⊢
  rw [st', len_stOf] at hi
  rw [h.bp, h.bx, addr_dest, st', dest_stOf hi]

-- `jnb` jumps: slot `d` is the top slot.
theorem Ap.short (hpre : Pre 96 A s) (h : Ap s ra t st1)
    (hc : (rd t.dmem t.regs.rbp.toBitVec).toNat ≤ (t.regs.rbx.toBitVec + 1#64).toNat) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have hd := h.d_lt hpre
  rw [h.len, h.bx, toNat_add_one _ hd] at hc
  have : ¬ ((rsi s).toNat + 1 < st1.len) := by omega
  rw [gen_ok h.hd h.hp]
  simp only [this, false_and, ↓reduceIte]

theorem Ap.dest_ne (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len)
    (hne : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 72#64) ≠
      t.regs.rbx.toBitVec) :
    st1.dest (rsi s).toNat ≠ (rsi s).toNat := by
  intro he
  apply hne
  apply BitVec.eq_of_toNat_eq
  rw [h.dest hi, he, h.bx]

-- `je` jumps: slot `d` has its own dest.
theorem Ap.self (h : Ap s ra t st1) (hi : (rsi s).toNat < st1.len)
    (hz : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rbx.toBitVec * 8#64 + 72#64) =
      t.regs.rbx.toBitVec) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have he := h.dest hi
  rw [hz, h.bx] at he
  rw [gen_ok h.hd h.hp]
  simp only [← he, ne_eq, not_true_eq_false, and_false, ↓reduceIte]

-- `jnb`, `je` or `ja` jumps to `.LB42` with `ok st1`.
theorem Ap.fin (h : Ap s ra t st1) (hg : generate (env s) (st s) (rsi s).toNat = .ok st1)
    (hu : u.dmem = t.dmem) (hax : u.regs.rax = t.regs.rax) (hrg : Rg s u) : At42 s ra u := by
  refine ⟨hu ▸ h.fm, hrg, ?_⟩
  unfold generateR
  rw [hg]
  refine ⟨by simp only [rax, Reg64s.get64_rax, hax, h.ax], ?_⟩
  rw [st', hu]; exact h.hst

-- The struct holds `st1` and slot `d` lies below the top slot.
theorem Ap.sw (hpre : Pre 96 generateA s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len) :
    Sw t.dmem t.regs.rbp.toBitVec t.regs.rbx.toBitVec st1 := by
  have hn : (env s).n = nOf t.dmem (rdi s) := by
    show (envOf s.dmem (rdi s)).n = _
    rw [n_envOf, h.fm.n hpre]
  refine ⟨h.bp ▸ h.fm.wf, ?_, ?_, ?_⟩
  · rw [h.bp]; exact h.hst
  · rw [h.bp, ← hn]; exact Pos.produce hpre.2.2.1 h.hd h.hp
  · rw [h.bx]; exact hlt

-- `jne` does not jump: the values are equal, and the four stores swap the dests.
theorem Ap.eq (hpre : Pre 96 generateA s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : (rd t.dmem (rd t.dmem (t.regs.rbp.toBitVec + 64#64) + t.regs.rbx.toBitVec * 8#64) ^^^
      rd t.dmem (rd t.dmem (t.regs.rbp.toBitVec + 64#64) +
        (rd t.dmem t.regs.rbp.toBitVec + -1#64) * 8#64)) <<< 16 = 0#64)
    (hu : u.dmem = swap4 t.dmem t.regs.rbp.toBitVec t.regs.rbx.toBitVec)
    (hax : u.regs.rax = t.regs.rax) (hrg : Rg s u) : At42 s ra u := by
  have hs := h.sw hpre hlt
  have hv' := hs.val.1 hv
  rw [h.bx] at hv'
  rw [h.bp] at hs hu
  refine ⟨hu ▸ h.fm.swap hpre hs, hrg, ?_⟩
  unfold generateR
  rw [gen_ok h.hd h.hp]
  simp only [hlt, ne_eq, hne, not_false_eq_true, and_self, hv', ↓reduceIte]
  refine ⟨by simp only [rax, Reg64s.get64_rax, hax, h.ax], ?_⟩
  rw [st', hu, hs.swap, h.bx]; rfl

-- `jne` jumps: the values differ.
theorem Ap.at44 (hpre : Pre 96 generateA s) (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : ¬ (rd t.dmem (rd t.dmem (t.regs.rbp.toBitVec + 64#64) + t.regs.rbx.toBitVec * 8#64) ^^^
      rd t.dmem (rd t.dmem (t.regs.rbp.toBitVec + 64#64) +
        (rd t.dmem t.regs.rbp.toBitVec + -1#64) * 8#64)) <<< 16 = 0#64)
    (hu : u.dmem = t.dmem) (hax : u.regs.rax = t.regs.rax) (hrg : Rg s u)
    (hdx : u.regs.rdx.toBitVec = rd t.dmem t.regs.rbp.toBitVec) : At44 s ra u := by
  have hv' : st1.val (rsi s).toNat ≠ st1.val (st1.len - 1) := by
    rw [← h.bx]; exact fun he => hv ((h.sw hpre hlt).val.2 he)
  refine ⟨st1, ⟨hu ▸ h.fm, hrg, h.hd, h.hp, by rw [st', hu]; exact h.hst, by rw [hax]; exact h.ax⟩,
    hlt, hne, hv', by rw [hdx, hu, hrg.bp, h.rg.bp]⟩

-- `ja` jumps: the top slot is too far.
theorem Ap.far (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : st1.val (rsi s).toNat ≠ st1.val (st1.len - 1))
    (hb : 16 < (rd t.dmem t.regs.rbp.toBitVec - t.regs.rbx.toBitVec - 1#64).toNat) :
    generate (env s) (st s) (rsi s).toNat = .ok st1 := by
  have hl := h.len_le
  have hL := h.len
  rw [h.bx] at hb
  have : ¬ st1.len - 1 - (rsi s).toNat ≤ MAX_SWAP_DEPTH := by
    simp only [MAX_SWAP_DEPTH]; rw [← hL] at hlt ⊢; bv_omega
  rw [gen_ok h.hd h.hp]
  simp only [hlt, ne_eq, hne, not_false_eq_true, and_self, hv, this, ↓reduceIte]

-- `ja` does not jump: `generate` calls `swapWith`.
theorem Ap.near (h : Ap s ra t st1) (hlt : (rsi s).toNat + 1 < st1.len)
    (hne : st1.dest (rsi s).toNat ≠ (rsi s).toNat)
    (hv : st1.val (rsi s).toNat ≠ st1.val (st1.len - 1))
    (hb : ¬ 16 < (rd t.dmem t.regs.rbp.toBitVec - t.regs.rbx.toBitVec - 1#64).toNat) :
    generate (env s) (st s) (rsi s).toNat = swapWith st1 (rsi s).toNat := by
  have hl := h.len_le
  have hL := h.len
  rw [h.bx] at hb
  have : st1.len - 1 - (rsi s).toNat ≤ MAX_SWAP_DEPTH := by
    simp only [MAX_SWAP_DEPTH]; rw [← hL] at hlt ⊢; bv_omega
  rw [gen_ok h.hd h.hp]
  simp only [hlt, ne_eq, hne, not_false_eq_true, and_self, hv, this, ↓reduceIte]

theorem Ap.ld (h : Ap s ra t st1) : (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true :=
  fm_isSome h.fm (by rw [h.rg.sp]; bv_omega)

-- The precondition of `swapWith`.
theorem Ap.pre (hpre : Pre 96 generateA s) (h : Ap s ra t st1) {c : MachineData} (hc : c.dmem = t.dmem)
    (hrg : Rg s c) (hdi : c.regs.rdi = c.regs.rbp) : Pre swapWithF swapWithA c := by
  have hrd := hrg.rdi hdi
  have henv := (h.fm.keeps hpre).1
  have hA := hpre.2.2
  obtain ⟨-, hops, -⟩ := produce_shape h.hp
  have hst := h.hst
  simp only [st'] at hst
  refine Kit.Fm.pre (k := 24) (by decide) hpre h.fm hc hrg.rsp hrd ⟨?_, ?_⟩
  all_goals simp only [st, env, cap, hrd, hc, henv, hst]
  · exact Pos.produce hA.1 h.hd h.hp
  · rw [← n_envOf, henv, n_envOf]; simp only [generateA, st, cap] at hA hops; omega

-- The state after the call of `swapWith`.
theorem Ap.after {c : MachineData} (hp : Post swapWithF swapWithR c u)
    (hag : (mod swapWithF c).Agree c u) (hpre : Pre 96 A s) (h : Ap s ra t st1)
    (hg : generate (env s) (st s) (rsi s).toNat = swapWith st1 (rsi s).toNat)
    (hc : c.dmem = t.dmem) (hrg : Rg s c) (hdi : c.regs.rdi = c.regs.rbp)
    (hsi : c.regs.rsi = c.regs.rbx) : At42 s ra u := by
  have hrd := hrg.rdi hdi
  refine ⟨Kit.Fm.call (k := 24) (by decide) (by decide) hpre h.fm hc hrg.rsp hrd hp hag,
    hrg.call hag, ?_⟩
  have h' := hp.2.2
  unfold swapWithR at h'
  rw [ok_congr hrd] at h'
  simp only [st, rsi, Reg64s.get64_rsi, hsi, hrg.bx, hrd, hc] at h'
  unfold generateR
  rw [hg, ← h.hst]
  exact h'

end

/-! ## The blocks `.LB42` and `.LB45` -/

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {A : MachineData → Prop}

theorem At42.ld0 (ht : At42 s ra t) : (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

theorem At42.ld8 (ht : At42 s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true :=
  fm_isSome ht.1 (by rw [ht.2.1.sp]; bv_omega)

theorem At42.sp (ht : At42 s ra t) (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64) :
    rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, ht.2.1.sp]; bv_omega

theorem At42.isSome (hpre : Pre 96 A s) (ht : At42 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64) : u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (hu ▸ ht.1.toMid) (ht.sp hsp)]; rfl

-- `pop rbx; pop rbp; ret` of `.LB42`.
theorem At42.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    (hpre : Pre 96 A s) (ht : At42 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hbx : u.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : u.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (hax : u.regs.rax = t.regs.rax) (h12 : u.regs.r12 = t.regs.r12) (h13 : u.regs.r13 = t.regs.r13)
    (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post generateF generateR s t ∧ (mod generateF s).Agree s t)
      u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  have hsp' := ht.sp hsp
  obtain ⟨hfm, hrg, hR⟩ := ht
  have hm : rd t.dmem (s.regs.rsp.toBitVec - 24#64) = s.regs.rbx.toBitVec := hfm.saved 1 (by decide)
  have hp : rd t.dmem (s.regs.rsp.toBitVec - 16#64) = s.regs.rbp.toBitVec := hfm.saved 0 (by decide)
  refine Kit.Fm.ret (by decide) hpre (hu ▸ hfm) hsp' (saved_regs ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hbx, hrg.sp, hm]
  · rw [hbp, hrg.sp, show s.regs.rsp.toBitVec - 24#64 + 8#64 = s.regs.rsp.toBitVec - 16#64 by
      bv_omega, hp]
  · rw [h12, hrg.r12]
  · rw [h13, hrg.r13]
  · rw [h14, hrg.r14]
  · rw [h15, hrg.r15]
  · intro t' hm' hax'
    exact res_ok hR (hm'.trans hu) (hax'.trans (by simp only [rax, Reg64s.get64_rax, hax]))

theorem At45.fm (hpre : Pre 96 A s) (ht : At45 s ra t) (hu : u.dmem = t.dmem) :
    Kit.Fm 96 [] s ra u.dmem := by
  rw [hu, ht.2.1]; exact Kit.Fm.init (by decide) hpre

theorem At45.sp (ht : At45 s ra t) (hsp : u.regs.rsp = t.regs.rsp) : rsp u = rsp s - 8#64 := by
  simp only [rsp, Reg64s.get64_rsp, hsp, ht.1]; rfl

theorem At45.isSome (hpre : Pre 96 A s) (ht : At45 s ra t) (hu : u.dmem = t.dmem)
    (hsp : u.regs.rsp = t.regs.rsp) : u.retAddr.isSome = true := by
  rw [Kit.Mid.retAddr (by decide) hpre (ht.fm hpre hu).toMid (ht.sp hsp)]; rfl

-- `mov rax, -2; ret` of `.LB45`.
theorem At45.ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    (hpre : Pre 96 A s) (ht : At45 s ra t) (hu : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hax : u.regs.rax.toBitVec = -2#64) (hbx : u.regs.rbx = t.regs.rbx)
    (hbp : u.regs.rbp = t.regs.rbp) (h12 : u.regs.r12 = t.regs.r12) (h13 : u.regs.r13 = t.regs.r13)
    (h14 : u.regs.r14 = t.regs.r14) (h15 : u.regs.r15 = t.regs.r15) :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post generateF generateR s t ∧ (mod generateF s).Agree s t)
      u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  refine Kit.Fm.ret (by decide) hpre (ht.fm hpre hu) (ht.sp hsp) (saved_regs ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hbx, ht.1]; rfl
  · rw [hbp, ht.1]; rfl
  · rw [h12, ht.1]; rfl
  · rw [h13, ht.1]; rfl
  · rw [h14, ht.1]; rfl
  · rw [h15, ht.1]; rfl
  · intro t' _ hax'
    unfold generateR
    rw [show generate (env s) (st s) (rsi s).toNat = .error .assertion by
      unfold generate; simp only [ht.2.2, ↓reduceIte]]
    exact hax'.trans (by simp only [rax, Reg64s.get64_rax, hax])

end

-- The flag of `jne` after `sal`.
theorem nz_res (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result v r) = !(v == 0#64) := by
  simp [CondCode.interp, StatusFlags.from_result]

end Generate

-- A hypothesis of type `t`, found with reducible unification only.
local macro "hyp% " t:term : term => `((by with_reducible assumption : $t))

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

open Generate

set_option maxHeartbeats 400000 in
theorem generate_body [Host] [FunDecls]
    (hprod : Spec "produce" produceF produceA produceR)
    (hswap : Spec "swapWith" swapWithF swapWithA swapWithR) :
    Body generateAsm generateF generateA generateR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 96 generateA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "generate", t => t = s.pushRa ra
      | .label ".LB42", t => At42 s ra t
      | .label ".LB44", t => At44 s ra t
      | .label ".LB45", t => At45 s ra t
      | _, _ => False)
    V ?_ rfl
  cfg_cases
  case left t ht => subst ht; kvcgen64
  case right.left t ht =>
    subst ht
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact e_ld3 hpre
    case vc2 =>
      have hc := (hyp% CondCode.nc.interp _ = true)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hc
      rw [e_n hpre] at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; simp [pushRa_rsp]
      · exact ⟨rfl, rfl, hc⟩
      · simp [V]
    case vc3 => exact e_ld16 hpre
    case vc4 => exact e_ld24 hpre
    case vc5 => exact e_ld32 hpre
    case vc6 =>
      have hc := (hyp% CondCode.nc.interp _ = false)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hc
      rw [e_n hpre] at hc
      exact produce_pre hpre rfl (e_rg rfl rfl rfl rfl rfl rfl rfl) rfl rfl hc
    all_goals
      have hc0 := (hyp% CondCode.nc.interp (StatusFlags.from_result (s.regs.rsi.toBitVec - _) _) = false)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hc0
      rw [e_n hpre] at hc0
      have hp := (hyp% Post produceF produceR _ _)
      have hag := (hyp% (mod produceF _).Agree _ _)
      obtain ⟨hfm, hrg, hres⟩ := after_produce hp hag hpre rfl (e_rg rfl rfl rfl rfl rfl rfl rfl) rfl rfl
      have hs := (hyp% CondCode.nz.interp (StatusFlags.from_result (_ &&& _) _) = _)
      rw [CondCode.interp_nz, ← CondCode.interp_z, Kit.z_test] at hs
    case vc7 =>
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hrg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact ⟨hfm, hrg.same rfl rfl rfl rfl rfl rfl rfl, res_ok (jne_taken hc0 hres (by simpa using hs)) rfl rfl⟩
      · simp [V]
    all_goals obtain ⟨st1, hap⟩ := jne_not hfm hrg hc0 hres (by simpa using hs)
    case vc8 => exact hap.ld0
    case vc9 =>
      have hc := (hyp% CondCode.nc.interp (StatusFlags.from_result (_ + 1#64 - _) _) = true)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.fin (hap.short hpre hc) rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
    all_goals
      have hc := (hyp% CondCode.nc.interp (StatusFlags.from_result (_ + 1#64 - _) _) = false)
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hc
      have hlt := hap.lt hpre hc
    case vc10 => exact hap.ld_dest hpre
    case vc11 =>
      have hz := (hyp% CondCode.z.interp (StatusFlags.from_result (rd _ (_ + 72#64) - _) _) = true)
      rw [Kit.z_sub, beq_iff_eq] at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.fin (hap.self (by omega) hz) rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
    all_goals
      have hz1 := (hyp% CondCode.z.interp (StatusFlags.from_result (rd _ (_ + 72#64) - _) _) = false)
      rw [Kit.z_sub, beq_eq_false_iff_ne] at hz1
      have hne := hap.dest_ne (by omega) hz1
      have hsw := hap.sw hpre hlt
    case vc12 => exact hap.ld8
    case vc13 => exact hsw.ld_val
    case vc14 => exact hsw.ld_top
    case vc15 => decide
    case vc16 =>
      have hv := (hyp% CondCode.nz.interp (StatusFlags.from_result ((_ : BitVec 64) <<< (16 : Nat)) _) = true)
      rw [nz_res, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hv
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.at44 hpre hlt hne hv rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl) rfl
      · simp [V]
    case vc17 => exact hsw.ld_b
    case vc18 => exact hsw.ld_a
    case vc19 => exact loadInt_isSome_store _ hsw.ld_b
    case vc20 => exact loadInt_isSome_store _ (loadInt_isSome_store _ hsw.ld_a)
    case vc21 =>
      exact loadInt_isSome_store _ (loadInt_isSome_store _ (hsw.ld_pos (by rw [hsw.rd2]; exact hsw.dest_b)))
    case vc22 =>
      exact loadInt_isSome_store _ (loadInt_isSome_store _ (loadInt_isSome_store _ (hsw.ld_pos hsw.dest_a)))
    case vc23 =>
      have hv := (hyp% CondCode.nz.interp (StatusFlags.from_result ((_ : BitVec 64) <<< (16 : Nat)) _) = false)
      rw [nz_res, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq] at hv
      exact hap.eq hpre hlt hne hv rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
    case vc24 => simp [V]
  case right.right.left t ht =>
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact ht.ld0
    case vc2 => exact ht.ld8
    case vc3 => exact ht.isSome hpre rfl rfl
    case vc4 => exact ht.ret hpre rfl rfl rfl rfl rfl rfl rfl rfl rfl
  case right.right.right.left t ht =>
    obtain ⟨st1, hap, hlt, hne, hv, hdx⟩ := ht
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 =>
      have hb := (hyp% CondCode.a.interp _ = true)
      rw [Kit.a_sub_imm _ _ (by decide), decide_eq_true_iff, hdx] at hb
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact (hap.rg.same rfl rfl rfl rfl rfl rfl rfl).stk
      · exact hap.fin (hap.far hlt hne hv hb) rfl rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl)
      · simp [V]
    case vc2 => exact hap.ld
    case vc3 => exact hap.pre hpre rfl (hap.rg.same rfl rfl rfl rfl rfl rfl rfl) rfl
    case vc4 =>
      have hb := (hyp% CondCode.a.interp _ = false)
      rw [Kit.a_sub_imm _ _ (by decide), decide_eq_false_iff_not, hdx] at hb
      have hp := (hyp% Post swapWithF swapWithR _ _)
      have hag := (hyp% (mod swapWithF _).Agree _ _)
      have h42 := hap.after hp hag hpre (hap.near hlt hne hv hb) rfl
        (hap.rg.same rfl rfl rfl rfl rfl rfl rfl) rfl rfl
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt; exact h42.2.1.stk
      · exact h42
      · simp [V]
  case right.right.right.right t ht =>
    kvcgen64 [hprod, hswap]
    all_goals bbu_norm at *
    case vc1 => exact ht.isSome hpre rfl rfl
    case vc2 => exact ht.ret hpre rfl rfl rfl rfl rfl rfl rfl rfl rfl

end Bbu
