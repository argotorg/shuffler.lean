module

public import FlatShuffler.Fn.Loop.Machine
import all FlatShuffler.Fn.Loop.Machine
public import FlatShuffler.Fn.Loop.Model
import all FlatShuffler.Fn.Loop.Model

@[expose] public section

/-!
Lemmas of the proof of the slot bound for `targetOffset` (`Fn/Loop/Bound.lean`): the
addresses of the struct words, the flags, the loads of the slot words, the inline swap,
and the invariants at the targets of the jumps for a state literal of `kvcgen64`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler

namespace Loop

/-! ## Words and flags -/

theorem addr_dest (S x : Word) : S + x * 8#64 + 56#64 = wordAt S (DEST + x.toNat) := by
  simp only [wordAt, DEST_eq]; bv_omega

theorem addr_pos (S x : Word) : S + x * 8#64 + 8248#64 = wordAt S (POS + x.toNat) := by
  simp only [wordAt, POS_eq]; bv_omega

theorem addr_data (D x : Word) : D + x * 8#64 = wordAt D x.toNat := by
  simp only [wordAt]; bv_omega

theorem addr_data8 (D x : Word) : D + x * 8#64 = D + BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

theorem ofNat_sub1 {k : Nat} (h : 0 < k) :
    BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  rw [BitVec.sub_eq_add_neg]; exact ofNat_pred h

-- The zero flag of a result `v`.
theorem z_res (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result v r) = (v == 0#64) := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem nz_res (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result v r) = !(v == 0#64) := by
  simp [CondCode.interp, StatusFlags.from_result]

-- The zero flag of `test v, v`.
theorem nz_and (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (v &&& v) r) = !(v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

/-! ## The model -/

-- One step of the search when `k` is not a movable copy of `b`.
theorem movFrom_no {st : St} {b k : Nat} (hk : b < k)
    (h : st.val k = st.val b → st.dest k = k) : movFrom st b k = movFrom st b (k - 1) := by
  rw [movFrom_step hk, ite_eq_right]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_and, Decidable.not_not]
  exact h

-- One step of the search when `k` is a movable copy of `b`.
theorem movFrom_yes {st : St} {b k : Nat} (hk : b < k) (hv : st.val k = st.val b)
    (hd : st.dest k ≠ k) : movFrom st b k = some k := by
  rw [movFrom_step hk, ite_eq_left]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨hv, hd⟩

-- The dest of a slot is below `n`.
theorem Pos.dest_lt {n : Nat} {st : St} (hp : Pos n st) {a : Nat} (ha : a < st.len) :
    st.dest a < n := by
  have ha' : a < st.dests.length := by rwa [St.length_dests]
  have h := positionOf_lt hp ((hp.iff _ a).2 ⟨ha', rfl⟩)
  rwa [St.dest_eq, getElem!_pos st.dests a ha']

/-! ## The struct words of a state -/

section
variable {s : MachineData} {ra : Int64} {t : MachineData}

theorem Base.len_le (hb : Base s ra t) : (st' s t).len ≤ nOf t.dmem (rdi s) := by
  rw [st', len_stOf]; exact hb.fm.wf.len_le

theorem Base.n_le (hb : Base s ra t) : nOf t.dmem (rdi s) ≤ 1024 := hb.fm.wf.n_le

-- A load of a word of the struct.
theorem Base.word_isSome (hb : Base s ra t) {a : Addr} {k : Nat} (ha : a = wordAt (rdi s) k)
    (hk : k < WORDS) : (t.dmem.loadInt a 8).isSome = true := by
  rw [ha]; exact hb.fm.wf.word_isSome hb.fm.wf.mapped hk

-- The pointer to `m_data`.
theorem Base.data (hb : Base s ra t) :
    rd t.dmem (t.regs.rbp.toBitVec + 24#64) = dataOf t.dmem (rdi s) := by
  rw [hb.rbp]; rfl

-- A load of the word of the slot `x`.
theorem Base.slot_isSome (hb : Base s ra t) {D x : Word} (hD : D = dataOf t.dmem (rdi s))
    (hx : x.toNat < (st' s t).len) : (t.dmem.loadInt (D + x * 8#64) 8).isSome = true := by
  have hw := hb.fm.wf
  have hl := hb.len_le
  have hd := hw.data_lt
  have hn := hw.n_le
  have : maxStackSize = 1024 := rfl
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr (Or.inl
    (inside_writable (Or.inr (Or.inr (Or.inl ?_))))))
  rw [hD]
  bv_omega

-- The slot `x`.
theorem slot_val {D x : Word} (hD : D = dataOf t.dmem (rdi s))
    (hx : x.toNat < (st' s t).len) :
    StackSlot.ofWord (rd t.dmem (D + x * 8#64)) = (st' s t).val x.toNat := by
  rw [st', len_stOf] at hx
  rw [st', val_stOf hx, hD, addr_data]

-- The dest word of the slot `x`.
theorem Base.dest (hb : Base s ra t) {x : Word} (hx : x.toNat < (st' s t).len) :
    (rd t.dmem (t.regs.rbp.toBitVec + x * 8#64 + 56#64)).toNat = (st' s t).dest x.toNat := by
  rw [st', len_stOf] at hx
  rw [hb.rbp, addr_dest, st', dest_stOf hx]

-- The `m_positionOf` word of `x`.
theorem Base.pos (hb : Base s ra t) {x : Word} (hx : x.toNat < nOf t.dmem (rdi s)) :
    optOf (rd t.dmem (t.regs.rbp.toBitVec + x * 8#64 + 8248#64)) = positionOf (st' s t) x.toNat := by
  rw [hb.rbp, addr_pos, st', positionOf_stOf hx]

-- The equal slots of `(a ^ b) << 16 == 0`.
theorem same {D x y : Word} (hD : D = dataOf t.dmem (rdi s))
    (hx : x.toNat < (st' s t).len) (hy : y.toNat < (st' s t).len) :
    (rd t.dmem (D + x * 8#64) ^^^ rd t.dmem (D + y * 8#64)) <<< 16 = 0#64
      ↔ (st' s t).val x.toNat = (st' s t).val y.toNat := by
  rw [← ofWord_eq_iff, slot_val hD hx, slot_val hD hy]

/-! ## The search of a copy -/

variable {T b : Nat}

theorem Copy.bounds (h : Copy s ra T b t) :
    (st' s t).len ≤ 1024 ∧ T ≤ (st' s t).len ∧ T < (env s).n ∧ (env s).n ≤ 1024 := by
  obtain ⟨h1, h2, h3, -⟩ := ctx_bounds h.2.2.2.2.2.2.2
  have : maxStackSize = 1024 := rfl
  exact ⟨by omega, h3, h.2.2.2.2.2.2.2.1, by omega⟩

-- `Copy` of a state literal with the registers of the search of `t`.
theorem copy_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax) (h2 : a2 = t.regs.rcx)
    (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) (h8 : a8 = t.regs.r8)
    (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) :
    Copy s ra T b ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hm h0 h2 h6 h7 h8 h14 h15
  obtain ⟨⟨hfm, hsp, hbp⟩, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨⟨hfm, hsp, hbp⟩, h1, h2, h3, h4, h5, h6, h7⟩

theorem at80_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hw : SrcWord s b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax)
    (h2 : a2 = t.regs.rcx) (h5 : a5 = t.regs.rdi) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp)
    (h8 : a8 = t.regs.r8) (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) {c : Nat}
    (hsi : a4.toBitVec = BitVec.ofNat 64 c) (hbc : b < c) (hc : c < (st' s t).len)
    (hst : step (env s) (st' s t) T
      = afterPos (st' s t) T b ((movFrom (st' s t) b c).getD b)) :
    At80 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hm h5
  exact ⟨T, b, c, copy_mk h rfl h0 h2 h6 h7 h8 h14 h15, hw, hsi, hbc, hc, hst⟩

theorem at78_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hw : SrcWord s b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax)
    (h2 : a2 = t.regs.rcx) (h5 : a5 = t.regs.rdi) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp)
    (h8 : a8 = t.regs.r8) (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) {c : Nat}
    (hsi : a4.toBitVec = BitVec.ofNat 64 c) (hbc : b < c) (hc : c < (st' s t).len)
    (hst : step (env s) (st' s t) T
      = afterPos (st' s t) T b ((movFrom (st' s t) b (c - 1)).getD b)) :
    At78 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hm h5
  exact ⟨T, b, c, copy_mk h rfl h0 h2 h6 h7 h8 h14 h15, hw, hsi, hbc, hc, hst⟩

theorem at90_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax)
    (h2 : a2 = t.regs.rcx) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp)
    (h8 : a8 = t.regs.r8) (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b b) :
    At90 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hm
  exact ⟨T, b, copy_mk h rfl h0 h2 h6 h7 h8 h14 h15, hst⟩

theorem at77_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax)
    (h2 : a2 = t.regs.rcx) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp)
    (h8 : a8 = t.regs.r8) (h14 : a14 = t.regs.r14) (h15 : a15 = t.regs.r15) {p : Nat}
    (hsi : a4.toBitVec = BitVec.ofNat 64 p) (hp : p < (st' s t).len)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b p) :
    At77 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hm
  exact ⟨T, b, p, copy_mk h rfl h0 h2 h6 h7 h8 h14 h15, hsi, hp, hst⟩

-- The variant of a state literal with the memory and `r14` of `t`: the part of the
-- loop is the same.
theorem outer_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hm : d = t.dmem) (k : Nat) :
    outer s ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ k
      = outer s t k := by
  subst hm; rfl

-- A load of the dest word of the slot `x`.
theorem Base.dest_isSome (hb : Base s ra t) {x : Word} (hx : x.toNat < 1024) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + x * 8#64 + 56#64) 8).isSome = true :=
  hb.word_isSome (by rw [hb.rbp, addr_dest]) (by simp only [DEST_eq, WORDS_eq]; omega)

-- The equal slots of `(src ^ a) << 16 == 0`, with the word of the slot `b` in `src`.
theorem same_src {D x : Word} (hD : D = dataOf t.dmem (rdi s)) {b : Nat}
    (hb : b < (st' s t).len) (hx : x.toNat < (st' s t).len) :
    (rd t.dmem (wordAt (dataOf t.dmem (rdi s)) b) ^^^ rd t.dmem (D + x * 8#64)) <<< 16 = 0#64
      ↔ (st' s t).val b = (st' s t).val x.toNat := by
  have hb' := hb
  rw [st', len_stOf] at hb'
  rw [← ofWord_eq_iff, slot_val hD hx, st', val_stOf hb']
end

/-! ## The inline swap, the call of `swapWith` and the variant -/

section
variable {s : MachineData} {ra : Int64} {t : MachineData} {T : Nat}

theorem Base.n_env (hpre : Pre loopF loopA s) (hb : Base s ra t) :
    (env s).n = nOf t.dmem (rdi s) := by
  rw [env, n_envOf, hb.fm.n hpre]

-- `Base` of a state literal with the memory and the fixed registers of `t`.
theorem base_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f}
    (h : Base s ra t) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) :
    Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, t.dmem⟩ := by
  subst h6 h7
  exact ⟨h.fm, h.rsp, h.rbp⟩

-- A load of the `m_positionOf` word of `x`.
theorem Base.pos_isSome (hb : Base s ra t) {x : Word} (hx : x.toNat < 1024) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + x * 8#64 + 8248#64) 8).isSome = true :=
  hb.word_isSome (by rw [hb.rbp, addr_pos]) (by simp only [POS_eq, WORDS_eq]; omega)

variable {a b : Nat}

theorem at75_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f}
    (hb : Base s ra t) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp)
    (h14 : a14.toBitVec = BitVec.ofNat 64 T) (hctx : Ctx s T (st' s t))
    (hpd : (st' s t).pendingGenerations ≠ 0)
    (hst : step (env s) (st' s t) T = (generate (env s) (st' s t) T).bind (afterGen T)) :
    At75 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, t.dmem⟩ :=
  ⟨base_mk hb h6 h7, T, h14, hctx, hpd, hst⟩

theorem at105_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f}
    (hb : Base s ra t) (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) (h14 : a14 = t.regs.r14)
    (h15 : a15 = t.regs.r15) (hl : t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len)
    (hT : t.regs.r14.toBitVec = BitVec.ofNat 64 T) (hctx : Ctx s T (st' s t)) {y : Word}
    (h0 : a0.toBitVec = y) (h2 : a2.toBitVec = rd t.dmem (t.regs.rbp.toBitVec + 24#64))
    (h8 : a8.toBitVec = y * 8#64)
    (h5 : a5.toBitVec = rd t.dmem (rd t.dmem (t.regs.rbp.toBitVec + 24#64) + y * 8#64))
    (hy : y.toNat < (st' s t).len)
    (hst : step (env s) (st' s t) T
      = afterPos (st' s t) T y.toNat ((movableCopy (st' s t) y.toNat).getD y.toNat)) :
    At105 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, t.dmem⟩ := by
  subst h14 h15
  refine ⟨T, y.toNat, ⟨base_mk hb h6 h7, hl, hT, ?_, ?_, ?_, hy, hctx⟩, ?_, hst⟩
  · rw [h0]; simp
  · rw [h2, hb.data]
  · rw [h8]; bv_omega
  · show a5.toBitVec = _
    rw [h5, hb.data, addr_data]

-- The word of `m_positionOf` for `T` is not `-1`: `T` is bound to the slot `y`.
theorem pos_some {o : Option Nat} {y : Word} (h : optOf y = o)
    (hne : y ≠ 18446744073709551615#64) : o = some y.toNat := by
  rw [← h]
  simp only [optOf]
  exact ite_eq_right hne

-- The flags of `.LB.Emission.buildBottomUp.5` when the jumps to `.LB.Emission.buildBottomUp.22` and `.LB.Emission.buildBottomUp.27` are not taken: the word
-- `y` of `m_positionOf` for `T` is a slot at or above `T`.
theorem bound_y {n T : Nat} {st : St} {x y : Word} {r : StatusFlags.from_result.Remaining} {af of : Bool}
    (hpY : optOf y = positionOf st T) (hp : Pos n st)
    (hz : CondCode.z.interp (StatusFlags.from_result (y - 18446744073709551615#64) r) = false)
    (hc : CondCode.c.interp (StatusFlags.from_result (y - x)
      { cf := (((y - x).toNat : Int) != (y.toNat : Int) - (x.toNat : Int)), af, of }) = false)
    (hx : x.toNat = T) :
    positionOf st T = some y.toNat ∧ y.toNat < st.len ∧ T ≤ y.toNat := by
  rw [Kit.z_sub, beq_eq_false_iff_ne] at hz
  simp only [CondCode.interp_c, StatusFlags.cf_from_result] at hc
  rw [Kit.cf_sub', hx] at hc
  have hsome := pos_some hpY hz
  exact ⟨hsome, positionOf_some hp hsome, hc⟩

-- `.LB.Emission.buildBottomUp.18` after the call of `swapWith`.
theorem at81_call {t' : MachineData} {z f} {q : St} (hB : Base s ra t')
    (h14 : t'.regs.r14.toBitVec = BitVec.ofNat 64 T) (hq : st' s t' = q)
    (hi : Iter s T (placeTop q T)) (hops : q.trace.length < cap s) (hp : Pos (env s).n q) :
    At81 s ra (MachineData.mk t'.regs z f t'.dmem) := by
  subst hq
  exact ⟨⟨hB.fm, hB.rsp, hB.rbp⟩, T, h14, hi, hops, hp⟩

-- `.LB.Emission.buildBottomUp.21` with explicit fields, so that the kernel does not compare the new
-- state with `t`.
theorem at108_far {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    {pos excess : Nat}
    (hB : Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩)
    (h4 : a4.toBitVec = BitVec.ofNat 64 pos) (h15 : a15.toBitVec - 17#64 = BitVec.ofNat 64 excess)
    {bst : St} (hR : R0 s = .error (.blocked pos excess bst)) :
    At108 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  ⟨hB, pos, excess, bst, h4, h15, hR⟩

-- The variant from `.LB.Emission.buildBottomUp.17` to `.LB.Emission.buildBottomUp.18`. The fields are explicit, so that the
-- kernel does not compare the new state with `t`.
theorem v81_swap {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a15 : UInt64} {z f d}
    (h : outer s ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, t.regs.r14, a15⟩,
      z, f, d⟩ t.regs.r14.toBitVec.toNat = outer s t t.regs.r14.toBitVec.toNat) :
    V s ".LB.Emission.buildBottomUp.18" ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, t.regs.r14, a15⟩,
      z, f, d⟩ < V s ".LB.Emission.buildBottomUp.17" t := by
  simp only [V, h]
  omega

-- The variant from `.LB.Emission.buildBottomUp.17` to `.LB.Emission.buildBottomUp.18` after the call of `swapWith`.
theorem v81_call {r : Reg64s} {z f d}
    (h : outer s ⟨r, z, f, d⟩ t.regs.r14.toBitVec.toNat = outer s t t.regs.r14.toBitVec.toNat)
    (h14 : r.r14 = t.regs.r14) :
    V s ".LB.Emission.buildBottomUp.18" ⟨r, z, f, d⟩ < V s ".LB.Emission.buildBottomUp.17" t := by
  simp only [V, h14, h]
  omega

-- The variant after the call of `swapWith`: the part of the loop is the same.
theorem outer_call {t' : MachineData} {z f}
    (hpd : (st' s t').pendingGenerations = (st' s t).pendingGenerations) (k : Nat) :
    outer s (MachineData.mk t'.regs z f t'.dmem) k = outer s t k := by
  show _ * 2048 + (st' s t').pendingGenerations = _
  rw [hpd]
  rfl

theorem v61 (u : MachineData) : V s ".LB.Emission.buildBottomUp.11" u = 0 := rfl

-- An error of `swapWith` gives `.LB.Emission.buildBottomUp.11`.
theorem at61_err {α : Type} {r : M α} {Q : α → Prop} {t' : MachineData} {z f}
    (hB : Base s ra t') (hR : ∀ e, r = .error e → R0 s = .error e) (h : Res (rdi s) r Q t')
    (hok : ∀ a, Q a → rax t' = 0#64) (hne : rax t' ≠ 0#64) :
    At61 s ra (MachineData.mk t'.regs z f t'.dmem) := by
  cases r with
  | ok a => exact absurd (hok a h) hne
  | error e =>
    refine ⟨hB.fm, hB.rsp, ?_⟩
    unfold loopR
    rw [show loop finishC (env s) (st s) 0 = R0 s from rfl, hR e rfl]
    cases e <;> exact h

end

end Loop

end FlatShuffler
