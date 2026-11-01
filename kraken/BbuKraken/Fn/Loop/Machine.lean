module

public import BbuKraken.Fn.Loop.Defs
import all BbuKraken.Fn.Loop.Defs

@[expose] public section

/-!
Machine lemmas of the old proof of `loop_body` (the C build, git 6f580e5): the frame, the calls, the stores to the
struct and to the local `urgentToDup`, and some word arithmetic.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

/-! ## Words -/

theorem msb_small {u : Nat} (h : u ≤ 1024) : (BitVec.ofNat 64 u).msb = false := by
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
  omega

theorem toNat_small {u : Nat} (h : u < 2 ^ 64) : (BitVec.ofNat 64 u).toNat = u := by
  simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_inj64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem ofNat_pred {k : Nat} (h : 0 < k) :
    BitVec.ofNat 64 k + -1#64 = BitVec.ofNat 64 (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 1 + -1#64 = 0#64 by decide, BitVec.add_zero]

theorem sub_of {L T : Nat} (hlt : T ≤ L) :
    BitVec.ofNat 64 L - BitVec.ofNat 64 T = BitVec.ofNat 64 (L - T) := by
  obtain ⟨j, rfl⟩ : ∃ j, L = j + T := ⟨L - T, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_sub_cancel]

-- `encU` is `-1` only for none.
theorem encU_m1 {n u : Nat} (hn : n ≤ 1024) (hu : u ≤ n) : encU n u = -1#64 ↔ u = n := by
  unfold encU
  split
  · simp_all
  · rename_i h
    simp only [h, iff_false]
    intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    have : (-1#64 : Word).toNat = 2 ^ 64 - 1 := by decide
    omega

/-! ## The frame -/

section
variable {s : MachineData} {ra : Int64} {t c t' : MachineData}

theorem stack_of (h : t.regs.rsp.toBitVec = rsp s - 80#64) :
    t.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, pushRa_rsp, h]
  bv_omega

-- `stack_of` for a state literal of `kvcgen64`.
theorem stack_mk {r : Reg64s} {z f d} (h : r.rsp.toBitVec = rsp s - 80#64) :
    (MachineData.mk r z f d).StackAtOrBelow (s.pushRa ra) :=
  stack_of h

-- The pops of `.LB.Emission.buildBottomUp.0` read the saved words.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) :
    rd m (rsp s - 56#64) = s.regs.rbx.toBitVec ∧ rd m (rsp s - 48#64) = s.regs.rbp.toBitVec
      ∧ rd m (rsp s - 40#64) = s.regs.r12.toBitVec ∧ rd m (rsp s - 32#64) = s.regs.r13.toBitVec
      ∧ rd m (rsp s - 24#64) = s.regs.r14.toBitVec
      ∧ rd m (rsp s - 16#64) = s.regs.r15.toBitVec :=
  ⟨h.saved 5 (by decide), h.saved 4 (by decide), h.saved 3 (by decide), h.saved 2 (by decide),
    h.saved 1 (by decide), h.saved 0 (by decide)⟩

/-! ## Calls -/

-- A callee at `rsp s - 80` keeps `Base`.
theorem Base.call {G : Nat} {R : MachineData → MachineData → Prop} (hG : 80 + G ≤ loopF)
    (hpre : Pre loopF loopA s) (hb : Base s ra t) (hp : Post G R c t')
    (hag : (mod G c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp) :
    Base s ra t' := by
  have hrsp : Bbu.rsp c = Bbu.rsp s - 80#64 := by
    simp only [Bbu.rsp, Reg64s.get64_rsp, hsp]; exact hb.rsp
  have hr := fun (q : Reg64) (hq : q ∉ (mod G c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h1 := hr .rsp (by decide)
  have h2 := hr .rbp (by decide)
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbp] at h1 h2
  refine ⟨Kit.Fm.call (k := 80) (by decide) hG hpre hb.fm hc hrsp hdi hp hag, ?_, ?_⟩
  · rw [h1, hsp]; exact hb.rsp
  · rw [h2, hbp]; exact hb.rbp

-- A callee keeps the registers that it saves.
theorem call_regs {G : Nat} (hag : (mod G c).Agree c t') :
    t'.regs.rbx = c.regs.rbx ∧ t'.regs.r12 = c.regs.r12 ∧ t'.regs.r13 = c.regs.r13
      ∧ t'.regs.r14 = c.regs.r14 ∧ t'.regs.r15 = c.regs.r15 := by
  have hr := fun (q : Reg64) (hq : q ∉ (mod G c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h1 := hr .rbx (by decide)
  have h2 := hr .r12 (by decide)
  have h3 := hr .r13 (by decide)
  have h4 := hr .r14 (by decide)
  have h5 := hr .r15 (by decide)
  simp only [Reg64s.get64_rbx, Reg64s.get64_r12, Reg64s.get64_r13, Reg64s.get64_r14,
    Reg64s.get64_r15] at h1 h2 h3 h4 h5
  exact ⟨UInt64.toBitVec_inj.mp h1, UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h3,
    UInt64.toBitVec_inj.mp h4, UInt64.toBitVec_inj.mp h5⟩

theorem env_call (hpre : Pre loopF loopA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : env c = env s := by
  show envOf c.dmem (rdi c) = _
  rw [hc, hdi]; exact (hb.fm.keeps hpre).1

theorem st_call (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) : st c = st' s t := by
  show stOf c.dmem (rdi c) = _
  rw [hc, hdi]

theorem cap_call (hpre : Pre loopF loopA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : cap c = cap s := by
  show 6 * nOf c.dmem (rdi c) = _
  rw [hc, hdi, hb.fm.n hpre]


theorem shallowestCopy_post (hp : Post shallowestCopyF shallowestCopyR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    rax t' = encOpt (shallowestCopyPosition (st' s t) (slot c)) ∧ st' s t' = st' s t := by
  have h := hp.2.2
  unfold shallowestCopyR at h
  rw [st_call hc hdi] at h
  exact ⟨h.1, by simpa only [st', hdi] using h.2⟩

end

/-! ## Stores to the struct -/

section
variable {s : MachineData} {ra : Int64} {m : Mem 64}

-- A store to `writable` keeps a word of the frame.
theorem rd_store_frame (hpre : Pre loopF loopA s) {a b : Addr}
    (ha : Mem.Blocks.Inside a 8 (writable s.dmem (rdi s)))
    (hb : Mem.Blocks.Inside b 8 [frame loopF s]) (v : Int) :
    rd (m.storeInt a 8 v) b = rd m b :=
  rd_storeInt_of_disjoint fun x hx hy => hpre.2.1.disj x (Kit.inside_bytes hb x hy)
    (inside_append.mpr (Or.inl (Kit.inside_bytes ha x hx)))

end

section
variable {m : Mem 64} {S : Addr} {k : Nat}

-- A word of `m_destinationOf` or `m_positionOf` is in `writable`.
theorem inside_word (hk1 : DEST ≤ k) (hk : k < WORDS) :
    Mem.Blocks.Inside (wordAt S k) 8 (writable m S) := by
  apply inside_writable
  simp only [wordAt, DEST_eq, WORDS_eq] at hk1 hk ⊢
  right; left
  constructor <;> bv_omega

-- The dest word of slot `i` is in `writable`.
theorem inside_dest {i : Nat} (hi : i < 1024) :
    Mem.Blocks.Inside (wordAt S (DEST + i)) 8 (writable m S) :=
  inside_word (Nat.le_add_right _ _) (by simp only [DEST_eq, WORDS_eq]; omega)

-- A store to a word of the struct keeps the other words of the struct.
theorem rd_store_word (hw : Wf m S) {j : Nat} (hk : k < WORDS) (hj : j < WORDS) (hne : j ≠ k)
    (v : Int) : rd (m.storeInt (wordAt S k) 8 v) (wordAt S j) = rd m (wordAt S j) :=
  rd_storeInt_of_disjoint (disjoint_wordAt (Ne.symm hne) hk hj hw.struct_lt)

-- A store to the dest word of slot `i` keeps the other words of the struct.
theorem rd_store_dest_other (hw : Wf m S) {i k : Nat} (hi : i < 1024) (hk : k < WORDS)
    (hne : k ≠ DEST + i) (v : Int) :
    rd (m.storeInt (wordAt S (DEST + i)) 8 v) (wordAt S k) = rd m (wordAt S k) :=
  rd_store_word hw (by simp only [DEST_eq, WORDS_eq]; omega) hk hne v

-- A store to a word of the struct keeps the working stack.
theorem rd_store_data (hw : Wf m S) (hk : k < WORDS) {i : Nat} (hi : i < nOf m S) (v : Int) :
    rd (m.storeInt (wordAt S k) 8 v) (wordAt (dataOf m S) i) = rd m (wordAt (dataOf m S) i) := by
  have hs := hw.struct_lt
  have hd := hw.data_lt
  refine rd_storeInt_of_disjoint fun x hx hy => hw.disj_struct x ?_ (Or.inl ?_)
  · simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hx hs hk ⊢; bv_omega
  · simp only [Mem.Blocks.Inside, or_false] at hy ⊢; bv_omega

-- A store to a word of the struct keeps the ops buffer.
theorem opOf_store_word (hw : Wf m S) (hk1 : DEST ≤ k) (hk : k < WORDS) {i : Nat}
    (hi : i < 6 * nOf m S) (v : Int) :
    opOf (m.storeInt (wordAt S k) 8 v) S i = opOf m S i := by
  have hs := hw.struct_lt
  have ho := hw.ops_lt
  have ho' : opsOf (m.storeInt (wordAt S k) 8 v) S = opsOf m S :=
    rd_store_word hw hk (by simp only [WORDS_eq]; omega) (by simp only [DEST_eq] at hk1; omega) v
  have hin : ∀ (a : Addr) (n : Nat), (a - opAt m S i).toNat + n ≤ 12 →
      Mem.Blocks.Disjoint [(wordAt S k, 8)] [(a, n)] := fun a n hc x hx hy =>
    hw.disj_struct x (by simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hx hs hk ⊢; bv_omega)
      (Or.inr (Or.inl (by simp only [Mem.Blocks.Inside, or_false] at hy; bv_omega)))
  simp only [opOf, opAt, ho']
  rw [rdb_storeInt_of_disjoint (hin _ 1 (by simp)), rdb_storeInt_of_disjoint (hin _ 1 (by bv_omega)),
    rd_storeInt_of_disjoint (hin _ 8 (by bv_omega))]

theorem val_set_self (st : St) (a b x : Nat) :
    ({ st with slots := st.slots.set a ⟨st.val a, x⟩ } : St).val b = st.val b := by
  simp only [St.val, List.getElem?_set]
  by_cases hb : b < st.slots.length <;> split <;> simp_all [Nat.not_lt.mpr]

-- The slots of `swapDestinations` before `m_positionOf` follows.
abbrev swapSlots (st : St) (a b : Nat) : St :=
  { st with slots := (st.slots.set a ⟨st.val a, st.dest b⟩).set b ⟨st.val b, st.dest a⟩ }

theorem swapSlots_dest_a (st : St) {a b : Nat} (ha : a < st.len) :
    (swapSlots st a b).dest a = if a = b then st.dest a else st.dest b := by
  simp only [St.len] at ha
  by_cases hab : a = b
  · subst hab; simp [St.dest, ha]
  · simp [St.dest, ha, hab, Ne.symm hab]

theorem swapSlots_dest_b (st : St) {a b : Nat} (hb : b < st.len) :
    (swapSlots st a b).dest b = st.dest a := by
  simp only [St.len] at hb
  simp [St.dest, hb]

theorem optOf_ofNat {a : Nat} (h : a < 2 ^ 64 - 1) : optOf (BitVec.ofNat 64 a) = some a := by
  have hm : (-1#64 : Word).toNat = 2 ^ 64 - 1 := by decide
  have ha : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  simp only [optOf]
  rw [ite_eq_right_iff.mpr fun he => by rw [he, hm] at ha; omega, ha]

end

/-! ## The inline swap -/

-- The memory after the inline `swapDestinations` of `.LB.Emission.buildBottomUp.5` and `.LB.Emission.buildBottomUp.17`: the dest words
-- of `a` and `b` change places, then the `m_positionOf` words of the two dests follow.
def swapMem (m : Mem 64) (S : Addr) (a b : Nat) : Mem 64 :=
  let va := rd m (wordAt S (DEST + a))
  let m2 := (m.storeInt (wordAt S (DEST + a)) 8 (rd m (wordAt S (DEST + b))).toInt).storeInt
    (wordAt S (DEST + b)) 8 va.toInt
  (m2.storeInt (wordAt S (POS + (rd m2 (wordAt S (DEST + a))).toNat)) 8
    (BitVec.ofNat 64 a).toInt).storeInt (wordAt S (POS + va.toNat)) 8 (BitVec.ofNat 64 b).toInt

section
variable {s : MachineData} {ra : Int64} {m : Mem 64}

end

end Loop

end Bbu
