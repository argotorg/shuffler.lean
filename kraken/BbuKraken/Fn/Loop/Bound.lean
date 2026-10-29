import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The slot bound for `T` in `buildBottomUp`: `.LB77` (`positionOf T`), the search of
a movable copy (`.LB109`, `.LB83`, `.LB81`, `.LB82`) and the swap of the dests (`.LB80`).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

/-! ## Helpers -/

-- A hypothesis of type `t`, found with reducible unification only.
local macro "hyp% " t:term : term => `((by with_reducible assumption : $t))

-- One form for the model state of `t` in all hypotheses and the goal.
local macro "nrm" : tactic => `(tactic| (try simp only [st', rdi, Reg64s.get64_rdi] at *))

theorem ofNat_sub1 {k : Nat} (h : 0 < k) :
    BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  rw [BitVec.sub_eq_add_neg]; exact ofNat_pred h

section
variable {s : MachineData} {ra : Int64} {t u : MachineData} {T b : Nat}

-- `Base` of a state with the same memory, `rsp` and `rbp`.
theorem Base.of (h : Base s ra t) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) : Base s ra u :=
  ⟨by rw [hm]; exact h.fm, by rw [hsp]; exact h.rsp, by rw [hbp]; exact h.rbp⟩

-- `Copy` of a state with the same memory and the same registers of the search.
theorem Copy.of (h : Copy s ra T b t) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h15 : u.regs.r15 = t.regs.r15)
    (h14 : u.regs.r14 = t.regs.r14) (hcx : u.regs.rcx = t.regs.rcx)
    (hax : u.regs.rax = t.regs.rax) : Copy s ra T b u := by
  have hs : st' s u = st' s t := by simp only [st', hm]
  obtain ⟨hb, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hb.of hm hsp hbp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h15, hs]; exact h1
  · rw [h14]; exact h2
  · rw [hcx]; exact h3
  · rw [hax, hs]; exact h4
  · rw [hs]; exact h5
  · rw [hs]; exact h6

-- `.LB80` from the search state `t`, with `p` in `rsi`.
theorem at80_of (h : Copy s ra T b t) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h15 : u.regs.r15 = t.regs.r15)
    (h14 : u.regs.r14 = t.regs.r14) (hcx : u.regs.rcx = t.regs.rcx)
    (hax : u.regs.rax = t.regs.rax) {p : Nat} (hsi : u.regs.rsi.toBitVec = BitVec.ofNat 64 p)
    (hp : p < (st' s t).len) (hv : (st' s t).val p = (st' s t).val b)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b p) : At80 s ra u := by
  have hs : st' s u = st' s t := by simp only [st', hm]
  exact ⟨T, b, p, h.of hm hsp hbp h15 h14 hcx hax, hsi, hs ▸ hp, hs ▸ hv, hs ▸ hst⟩

-- `.LB83` from the search state `t`, with `b` in `rsi` and `k` in `rdx`.
theorem at83_of (h : Copy s ra T b t) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h15 : u.regs.r15 = t.regs.r15)
    (h14 : u.regs.r14 = t.regs.r14) (hcx : u.regs.rcx = t.regs.rcx)
    (hax : u.regs.rax = t.regs.rax) {k : Nat} (hsi : u.regs.rsi.toBitVec = BitVec.ofNat 64 b)
    (hdx : u.regs.rdx.toBitVec = BitVec.ofNat 64 k) (hbk : b < k) (hk : k < (st' s t).len)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b ((movFrom (st' s t) b k).getD b)) :
    At83 s ra u := by
  have hs : st' s u = st' s t := by simp only [st', hm]
  exact ⟨T, b, k, h.of hm hsp hbp h15 h14 hcx hax, hsi, hdx, hbk, hs ▸ hk, hs ▸ hst⟩

-- `.LB81` from the search state `t`, with `b` in `rsi` and `k` in `rdx`.
theorem at81_of (h : Copy s ra T b t) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hbp : u.regs.rbp = t.regs.rbp) (h15 : u.regs.r15 = t.regs.r15)
    (h14 : u.regs.r14 = t.regs.r14) (hcx : u.regs.rcx = t.regs.rcx)
    (hax : u.regs.rax = t.regs.rax) {k : Nat} (hsi : u.regs.rsi.toBitVec = BitVec.ofNat 64 b)
    (hdx : u.regs.rdx.toBitVec = BitVec.ofNat 64 k) (hbk : b < k) (hk : k < (st' s t).len)
    (hst : step (env s) (st' s t) T
      = afterPos (st' s t) T b ((movFrom (st' s t) b (k - 1)).getD b)) : At81 s ra u := by
  have hs : st' s u = st' s t := by simp only [st', hm]
  exact ⟨T, b, k, h.of hm hsp hbp h15 h14 hcx hax, hsi, hdx, hbk, hs ▸ hk, hs ▸ hst⟩

theorem addr_stack (S x : BitVec 64) : S + x * 8#64 + 64#64 = wordAt S (STACK + x.toNat) := by
  simp only [wordAt, STACK]; bv_omega

theorem addr_dest (S x : BitVec 64) : S + x * 8#64 + 8256#64 = wordAt S (DEST + x.toNat) := by
  simp only [wordAt, DEST_eq]; bv_omega

-- The value word of the slot `x`.
theorem Base.val (h : Base s ra t) {x : Word} (hx : x.toNat < (st' s t).len) :
    rd t.dmem (t.regs.rbp.toBitVec + x * 8#64 + 64#64) = (st' s t).val x.toNat := by
  rw [h.rbp, addr_stack, val_stOf (by rwa [len_stOf] at hx)]

-- The dest word of the slot `x`.
theorem Base.dest (h : Base s ra t) {x : Word} (hx : x.toNat < (st' s t).len) :
    (rd t.dmem (t.regs.rbp.toBitVec + x * 8#64 + 8256#64)).toNat = (st' s t).dest x.toNat := by
  rw [h.rbp, addr_dest, dest_stOf (by rwa [len_stOf] at hx)]

-- The loads of the value and the dest words of the slot `x`.
theorem Base.isSome (h : Base s ra t) {x : Word} (k : Word) (hk : k = 64#64 ∨ k = 8256#64)
    (hx : x.toNat < (st' s t).len) :
    (t.dmem.loadInt (t.regs.rbp.toBitVec + x * 8#64 + k) 8).isSome = true := by
  have hw := h.fm.wf
  have hl : (rd t.dmem (wordAt (rdi s) 0)).toNat ≤ 1024 := hw.len_le
  rw [st', len_stOf] at hx
  rw [h.rbp]
  rcases hk with rfl | rfl
  · rw [addr_stack]; exact hw.word_isSome hw.mapped (by simp only [STACK, WORDS_eq]; omega)
  · rw [addr_dest]; exact hw.word_isSome hw.mapped (by simp only [DEST_eq, WORDS_eq]; omega)

/-! Lemmas for a state literal of `kvcgen64`. On such a literal `u`, `rfl : u.regs.rsp = t.regs.rsp`
makes the kernel compare `u.regs` with `t.regs` field by field. Here the fields are variables,
so it does not. -/

theorem at80_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax) (h2 : a2 = t.regs.rcx)
    (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) (h14 : a14 = t.regs.r14)
    (h15 : a15 = t.regs.r15) {p : Nat} (hsi : a4.toBitVec = BitVec.ofNat 64 p)
    (hp : p < (st' s t).len) (hv : (st' s t).val p = (st' s t).val b)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b p) :
    At80 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  at80_of h hm h6 h7 h15 h14 h2 h0 hsi hp hv hst

theorem at83_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax) (h2 : a2 = t.regs.rcx)
    (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) (h14 : a14 = t.regs.r14)
    (h15 : a15 = t.regs.r15) {k : Nat} (hsi : a4.toBitVec = BitVec.ofNat 64 b)
    (hdx : a3.toBitVec = BitVec.ofNat 64 k) (hbk : b < k) (hk : k < (st' s t).len)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b ((movFrom (st' s t) b k).getD b)) :
    At83 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  at83_of h hm h6 h7 h15 h14 h2 h0 hsi hdx hbk hk hst

theorem at81_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hm : d = t.dmem) (h0 : a0 = t.regs.rax) (h2 : a2 = t.regs.rcx)
    (h6 : a6 = t.regs.rsp) (h7 : a7 = t.regs.rbp) (h14 : a14 = t.regs.r14)
    (h15 : a15 = t.regs.r15) {k : Nat} (hsi : a4.toBitVec = BitVec.ofNat 64 b)
    (hdx : a3.toBitVec = BitVec.ofNat 64 k) (hbk : b < k) (hk : k < (st' s t).len)
    (hst : step (env s) (st' s t) T
      = afterPos (st' s t) T b ((movFrom (st' s t) b (k - 1)).getD b)) :
    At81 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  at81_of h hm h6 h7 h15 h14 h2 h0 hsi hdx hbk hk hst

-- The variant at `.LB83` with `rdx = k` is below the one at `.LB109`. The state has
-- variable fields, so the kernel does not unfold the literal of `kvcgen64`.
theorem v83_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    {k : Nat} (hm : d = t.dmem) (h14 : a14 = t.regs.r14)
    (h3 : a3.toBitVec = BitVec.ofNat 64 k) (hk : k < 1024) :
    V s ".LB83" ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      < V s ".LB109" t := by
  subst hm h14
  simp only [V, outer, st', h3, toNat_small (show k < 2 ^ 64 by omega)]
  omega

theorem Copy.bounds (h : Copy s ra T b t) :
    (st' s t).len ≤ 1024 ∧ T ≤ (st' s t).len ∧ T < (env s).n := by
  obtain ⟨h1, h2, h3, -⟩ := ctx_bounds h.2.2.2.2.2.2
  have : MAX_N = 1024 := rfl
  exact ⟨by omega, h3, h.2.2.2.2.2.2.1⟩

/-! ## `.LB80` -/

-- The memory after the two stores of `.LB80`: the dests of `rsi` and `rcx` change places.
def mem80 (t : MachineData) : Mem 64 :=
  (t.dmem.storeInt (t.regs.rbp.toBitVec + (t.regs.rsi.toBitVec + 1032#64) * 8#64) 8
      (rd t.dmem (t.regs.rcx.toBitVec + 8256#64)).toInt).storeInt
    (t.regs.rcx.toBitVec + 8256#64) 8
    (rd t.dmem (t.regs.rbp.toBitVec + (t.regs.rsi.toBitVec + 1032#64) * 8#64)).toInt

-- The two addresses of the stores of `.LB80`.
theorem addr80 (h : Copy s ra T b t) {p : Nat} (hsi : t.regs.rsi.toBitVec = BitVec.ofNat 64 p) :
    t.regs.rbp.toBitVec + (t.regs.rsi.toBitVec + 1032#64) * 8#64 = wordAt (rdi s) (DEST + p)
      ∧ t.regs.rcx.toBitVec + 8256#64 = wordAt (rdi s) (DEST + b) := by
  rw [h.1.rbp, hsi, h.2.2.2.1]
  simp only [wordAt, DEST_eq]
  constructor <;> bv_omega

-- The stores of `.LB80` keep `Fm` and give `swapDestinations`.
theorem Copy.swap80 (hpre : Pre loopF loopA s) (h : Copy s ra T b t) {p : Nat}
    (hsi : t.regs.rsi.toBitVec = BitVec.ofNat 64 p) (hp : p < (st' s t).len) :
    Fm s ra (mem80 t) ∧ stOf (mem80 t) (rdi s) = swapDestinations (st' s t) p b := by
  have hb := h.2.2.2.2.2.1
  obtain ⟨e1, e2⟩ := addr80 h hsi
  have hp' : p < (rd t.dmem (wordAt (rdi s) 0)).toNat := by rwa [st', len_stOf] at hp
  have hb' : b < (rd t.dmem (wordAt (rdi s) 0)).toNat := by rwa [st', len_stOf] at hb
  have hs := h.1.fm.swap hpre hp hb (dest_stOf hp').symm (dest_stOf hb').symm
  unfold mem80
  rw [e1, e2]
  exact ⟨hs.1, hs.2.1⟩

-- A load of a dest word.
theorem Fm.dest_isSome {m : Mem 64} (h : Fm s ra m) {i : Nat} (hi : i < 1024) :
    (m.loadInt (wordAt (rdi s) (DEST + i)) 8).isSome = true :=
  h.wf.word_isSome h.wf.mapped (by simp only [DEST_eq, WORDS_eq]; omega)

theorem base_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hfm : Fm s ra d) (h6 : a6.toBitVec = rsp s - 80#64) (h7 : a7.toBitVec = rdi s) :
    Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  ⟨hfm, h6, h7⟩

-- `.LB95` after the swap at `p = T`.
theorem at95_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : Copy s ra T b t) (hfm : Fm s ra d) (hd : stOf d (rdi s) = swapDestinations (st' s t) T b)
    (h6 : a6.toBitVec = rsp s - 80#64) (h7 : a7.toBitVec = rdi s)
    (hsi : a4.toBitVec = BitVec.ofNat 64 T)
    (hst : step (env s) (st' s t) T = afterPos (st' s t) T b T) :
    At95 s ra
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  have hit := iter_next (s := s) ⟨st' s t, h.2.2.2.2.2.2, hst.trans (ap_self rfl)⟩
  refine ⟨base_mk hfm h6 h7, T + 1, by rw [hsi]; exact (BitVec.ofNat_add T 1).symm, ?_⟩
  show InvL (env s) (stOf d (rdi s)) (T + 1) ∧ loop (env s) (stOf d (rdi s)) (T + 1) = R0 s
  rw [hd]
  exact hit

-- `.LB84` from an iteration that gives `placeTop` of the state of `u`.
theorem at84_of (hb : Base s ra u) (h14 : u.regs.r14.toBitVec = BitVec.ofNat 64 T) {st0 : St}
    (hctx : Ctx s T st0) (hit : step (env s) st0 T = placeTop (st' s u) T)
    (hops : (st' s u).trace.length ≤ st0.trace.length + 1) : At84 s ra u := by
  have h1 := (ctx_bounds hctx).2.2.2
  have h2 : (env s).n = nOf s.dmem (rdi s) := n_envOf
  refine ⟨hb, T, h14, ⟨st0, hctx, hit⟩, ?_⟩
  show _ < 6 * nOf s.dmem (rdi s)
  omega

theorem at84_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hfm : Fm s ra d) (h6 : a6.toBitVec = rsp s - 80#64) (h7 : a7.toBitVec = rdi s)
    (h14 : a14.toBitVec = BitVec.ofNat 64 T) {st0 : St} (hctx : Ctx s T st0)
    (hit : step (env s) st0 T = placeTop (stOf d (rdi s)) T)
    (hops : (stOf d (rdi s)).trace.length ≤ st0.trace.length + 1) :
    At84 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  at84_of (base_mk hfm h6 h7) h14 hctx hit hops

theorem at110_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hfm : Fm s ra d) (h6 : a6.toBitVec = rsp s - 80#64) (h7 : a7.toBitVec = rdi s) {c k : Nat}
    (hsi : a4.toBitVec = BitVec.ofNat 64 c) (h15 : a15.toBitVec - 17#64 = BitVec.ofNat 64 k)
    (hr : R0 s = .error (.blocked c k)) :
    At110 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  ⟨base_mk hfm h6 h7, c, k, hsi, h15, hr⟩

-- The precondition of `swapWith`.
theorem swapA_mk (hpre : Pre loopF loopA s)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hfm : Fm s ra d) (h5 : a5.toBitVec = rdi s)
    (hops : (stOf d (rdi s)).trace.length < 6 * (env s).n) :
    swapWithA
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  unfold swapWithA
  show (stOf d a5.toBitVec).trace.length < 6 * nOf d a5.toBitVec
  rw [h5, hfm.n hpre, ← n_envOf]
  exact hops

-- The precondition of the call of `swapWith`.
theorem swapPre_mk (hpre : Pre loopF loopA s)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hfm : Fm s ra d) (h6 : a6.toBitVec = rsp s - 80#64) (h5 : a5.toBitVec = rdi s)
    (hops : (stOf d (rdi s)).trace.length < 6 * (env s).n) :
    Pre swapWithF swapWithA
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  Kit.Fm.pre (k := 80) (by decide) hpre hfm rfl h6 h5 (swapA_mk hpre hfm h5 hops)

-- The call of `swapWith` from a state literal: `Base` after the call, the result, and `r14`.
theorem swap_call_mk (hpre : Pre loopF loopA s)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d} {t' : MachineData}
    (hfm : Fm s ra d) (h6 : a6.toBitVec = rsp s - 80#64) (h7 : a7.toBitVec = rdi s)
    (h5 : a5.toBitVec = rdi s)
    (hp : Post swapWithF swapWithR
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ t')
    (hag : (mod swapWithF
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩).Agree
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ t') :
    Base s ra t'
      ∧ Res (rdi s) (swapWith (stOf d (rdi s)) a4.toBitVec.toNat)
          (fun r => rax t' = 0#64 ∧ st' s t' = r) t'
      ∧ t'.regs.r14 = a14 := by
  have hb := Base.call (by decide) hpre (base_mk hfm h6 h7) hp hag rfl rfl h5 rfl
  have hg := swapWith_post hp rfl h5
  exact ⟨hb, hg, (call_regs hag).2.2.2.1⟩

-- The variant from `.LB80` to `.LB95` at `p = T`.
theorem v95_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hd : (stOf d (rdi s)).pendingGenerations = (st' s t).pendingGenerations)
    (hsi : a4.toBitVec = BitVec.ofNat 64 T)
    (h14 : t.regs.r14.toBitVec = BitVec.ofNat 64 T) (hT : T < (env s).n) (hn : (env s).n ≤ 1024) :
    V s ".LB95" ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      < V s ".LB80" t := by
  have e : (BitVec.ofNat 64 T + 1#64).toNat = T + 1 := by
    rw [← BitVec.ofNat_add]; exact toNat_small (by omega)
  simp only [V, outer, st', hsi, h14, e, toNat_small (show T < 2 ^ 64 by omega), hd, W]
  omega

-- The variant from `.LB80` to `.LB84`.
theorem v84_of (hd : (st' s u).pendingGenerations = (st' s t).pendingGenerations)
    (h14 : u.regs.r14 = t.regs.r14) :
    V s ".LB84" u < V s ".LB80" t := by
  simp only [V, outer, hd, h14]
  omega

theorem v84_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hd : (stOf d (rdi s)).pendingGenerations = (st' s t).pendingGenerations)
    (h14 : a14 = t.regs.r14) :
    V s ".LB84" ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      < V s ".LB80" t :=
  v84_of hd h14

-- A failed `swapWith` gives `.LB65`.
theorem swap_err (hb : Base s ra t) {st0 X : St} {p : Nat} (hctx : Ctx s T st0)
    (hstep : step (env s) st0 T = (swapWith X p).bind (placeTop · T))
    (hg : Res (rdi s) (swapWith X p) (fun r => rax t = 0#64 ∧ st' s t = r) t)
    (hnz : rax t ≠ 0#64) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hax : rax u = rax t) : At65 s ra u := by
  cases hr : swapWith X p with
  | ok r => rw [hr] at hg; exact absurd hg.1 hnz
  | error e =>
    rw [hr] at hg
    have he := iter_err (s := s) ⟨st0, hctx, by rw [hstep, hr]; rfl⟩
    refine ⟨hm ▸ hb.fm, hsp ▸ hb.rsp, ?_⟩
    unfold loopR
    rw [show loop (env s) (st s) 0 = R0 s from rfl, he]
    cases e with
    | blocked p x =>
      show rax u = _ ∧ _
      rw [hax, hm]; exact hg
    | assertion =>
      show rax u = _
      rw [hax]; exact hg

-- The variant from `.LB80` to `.LB110` and to `.LB65`.
theorem v110_lt : V s ".LB110" u < V s ".LB80" t := by simp only [V]; omega

theorem v65_lt : V s ".LB65" u < V s ".LB80" t := by simp [V]

-- The zero flag of `test v, v`.
private theorem nz_and (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (v &&& v) r) = !(v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

/-! ## `.LB77` -/

-- `encOpt` of a slot `≤ 1024` is not `-1`.
theorem encOpt_none {o : Option Nat} {x : Word} (hax : x = encOpt o)
    (hz : x = 18446744073709551615#64) (h : ∀ b, o = some b → b ≤ 1024) : o = none := by
  cases o with
  | none => rfl
  | some b =>
    have := h b rfl
    rw [hax, encOpt,
      show (18446744073709551615#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 1) by decide] at hz
    exact absurd (ofNat_inj64 (by omega) (by decide) hz) (by omega)

theorem encOpt_some {o : Option Nat} {x : Word} (hax : x = encOpt o)
    (hz : x ≠ 18446744073709551615#64) : ∃ b, o = some b ∧ x = BitVec.ofNat 64 b := by
  cases o with
  | none => exact absurd (hax.trans (by decide)) hz
  | some b => exact ⟨b, rfl, hax⟩

-- The state after the call of `positionOf T` at `.LB77`.
theorem post77 (hpre : Pre loopF loopA s) (hb : Base s ra t) {S : St} (hS : st' s t = S)
    (hT : T ≤ 1024) {c t' : MachineData}
    (hp : Post positionOfF positionOfR c t') (hag : (mod positionOfF c).Agree c t')
    (hc : c.dmem = t.dmem) (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s)
    (hbp : c.regs.rbp = t.regs.rbp) (hsi : rsi c = BitVec.ofNat 64 T)
    (hc14 : c.regs.r14 = t.regs.r14) (hc15 : c.regs.r15 = t.regs.r15) :
    Base s ra t' ∧ st' s t' = S ∧ t'.regs.r14 = t.regs.r14 ∧ t'.regs.r15 = t.regs.r15
      ∧ t'.regs.rax.toBitVec = encOpt (positionOf S T) := by
  have hb' := Base.call (by decide) hpre hb hp hag hc hsp hdi hbp
  have h := positionOf_post hp hc hdi
  rw [hsi, toNat_small (by omega), hS] at h
  obtain ⟨-, -, -, e14, e15⟩ := call_regs hag
  exact ⟨hb', h.2, e14.trans hc14, e15.trans hc15, h.1⟩

-- The words of the slots `b` (in `rax`) and `T` (in `r14`).
theorem slots77 (hb : Base s ra u) {S : St} (hu : st' s u = S)
    (h14 : u.regs.r14.toBitVec = BitVec.ofNat 64 T) (hax : u.regs.rax.toBitVec = BitVec.ofNat 64 b)
    (hT : T < S.len) (hbl : b < S.len) (hl : S.len ≤ 1024) :
    rd u.dmem (u.regs.rbp.toBitVec + u.regs.rax.toBitVec * 8#64 + 64#64) = S.val b
      ∧ rd u.dmem (u.regs.rbp.toBitVec + u.regs.r14.toBitVec * 8#64 + 64#64) = S.val T
      ∧ u.regs.rbp.toBitVec + u.regs.rax.toBitVec * 8#64 = wordAt (rdi s) b
      ∧ u.regs.rbp.toBitVec + (u.regs.r14.toBitVec + 1032#64) * 8#64 = wordAt (rdi s) (DEST + T)
      ∧ u.regs.rbp.toBitVec + u.regs.rax.toBitVec * 8#64 + 8256#64 = wordAt (rdi s) (DEST + b) := by
  have xb : u.regs.rax.toBitVec.toNat = b := by rw [hax]; exact toNat_small (by omega)
  have xT : u.regs.r14.toBitVec.toNat = T := by rw [h14]; exact toNat_small (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hb.val (by rw [xb, hu]; exact hbl), hu, xb]
  · rw [hb.val (by rw [xT, hu]; exact hT), hu, xT]
  · rw [hb.rbp, hax]; simp only [wordAt]; bv_omega
  · rw [hb.rbp, hax, h14]; simp only [wordAt, DEST_eq]; constructor <;> bv_omega

-- The memory after the two stores of `.LB77`: the dests of `T` and `b` change places.
def mem77 (t : MachineData) : Mem 64 :=
  (t.dmem.storeInt (t.regs.rbp.toBitVec + (t.regs.r14.toBitVec + 1032#64) * 8#64) 8
      (rd t.dmem (t.regs.rbp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8256#64)).toInt).storeInt
    (t.regs.rbp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8256#64) 8
    (rd t.dmem (t.regs.rbp.toBitVec + (t.regs.r14.toBitVec + 1032#64) * 8#64)).toInt

-- The stores of `.LB77` keep `Fm` and give `swapDestinations`.
theorem swap77 (hpre : Pre loopF loopA s) (hb : Base s ra u) {S : St} (hu : st' s u = S)
    (e1 : u.regs.rbp.toBitVec + (u.regs.r14.toBitVec + 1032#64) * 8#64 = wordAt (rdi s) (DEST + T))
    (e2 : u.regs.rbp.toBitVec + u.regs.rax.toBitVec * 8#64 + 8256#64 = wordAt (rdi s) (DEST + b))
    (hT : T < S.len) (hbl : b < S.len) :
    Fm s ra (mem77 u) ∧ stOf (mem77 u) (rdi s) = swapDestinations S T b := by
  subst hu
  have hT' : T < (rd u.dmem (wordAt (rdi s) 0)).toNat := by rwa [st', len_stOf] at hT
  have hb' : b < (rd u.dmem (wordAt (rdi s) 0)).toNat := by rwa [st', len_stOf] at hbl
  have hs := hb.fm.swap hpre hT hbl (dest_stOf hT').symm (dest_stOf hb').symm
  unfold mem77
  rw [e1, e2]
  exact ⟨hs.1, hs.2.1⟩

-- `.LB78`: no slot is bound for `T`.
theorem at78_of (hb : Base s ra u) (h14 : u.regs.r14.toBitVec = BitVec.ofNat 64 T) {S : St}
    (hu : st' s u = S) (hctx : Ctx s T S) (hpd : S.pendingGenerations ≠ 0)
    (hst : step (env s) S T = bound (env s) S T) (hn : positionOf S T = none) : At78 s ra u := by
  subst hu
  exact ⟨hb, T, h14, hctx, hpd, by rw [hst, bound_none hn]⟩

-- `.LB109`: the slot `b` is bound for `T`.
theorem at109_of (hb : Base s ra u) {S : St} (hu : st' s u = S)
    (h15 : u.regs.r15.toBitVec = BitVec.ofNat 64 S.len)
    (h14 : u.regs.r14.toBitVec = BitVec.ofNat 64 T) (hcx : u.regs.rcx.toBitVec = wordAt (rdi s) b)
    (hax : u.regs.rax.toBitVec = S.val b) (hbl : b < S.len) (hctx : Ctx s T S)
    (hsi : u.regs.rsi.toBitVec = BitVec.ofNat 64 b)
    (hst : step (env s) S T = afterPos S T b ((movableCopy S b).getD b)) : At109 s ra u := by
  subst hu
  exact ⟨T, b, ⟨hb, h15, h14, hcx, hax, hbl, hctx⟩, hsi, hst⟩

-- `.LB68` after the swap of the dests of `T` and `b`.
theorem at68_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (hfm : Fm s ra d) (h6 : a6.toBitVec = rsp s - 80#64) (h7 : a7.toBitVec = rdi s)
    (h14 : a14.toBitVec = BitVec.ofNat 64 T)
    (hit : InvL (env s) (stOf d (rdi s)) (T + 1) ∧ loop (env s) (stOf d (rdi s)) (T + 1) = R0 s) :
    At68 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  ⟨base_mk hfm h6 h7, T + 1, by rw [h14]; exact (BitVec.ofNat_add T 1).symm, hit⟩

-- The variants from `.LB77` to `.LB78`, `.LB109` and `.LB92`.
theorem v77_of {S : St} (hu : st' s u = S) (ht : st' s t = S) (h14 : u.regs.r14 = t.regs.r14) :
    V s ".LB78" u < V s ".LB77" t ∧ V s ".LB109" u < V s ".LB77" t
      ∧ V s ".LB92" u < V s ".LB77" t := by
  simp only [V, outer, hu, ht, h14]
  omega

theorem v77_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    {S : St} (hu : stOf d (rdi s) = S) (ht : st' s t = S) (h14 : a14 = t.regs.r14) :
    let u : MachineData :=
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
    V s ".LB78" u < V s ".LB77" t ∧ V s ".LB109" u < V s ".LB77" t
      ∧ V s ".LB92" u < V s ".LB77" t :=
  v77_of hu ht h14

-- The variant from `.LB77` to `.LB68`.
theorem v68_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    {S : St} (hd : (stOf d (rdi s)).pendingGenerations = S.pendingGenerations) (ht : st' s t = S)
    (h14 : a14.toBitVec = BitVec.ofNat 64 T) (h14t : t.regs.r14.toBitVec = BitVec.ofNat 64 T)
    (hT : T < (env s).n) (hn : (env s).n ≤ 1024) :
    V s ".LB68" ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      < V s ".LB77" t := by
  have e : (BitVec.ofNat 64 T + 1#64).toNat = T + 1 := by
    rw [← BitVec.ofNat_add]; exact toNat_small (by omega)
  simp only [st'] at ht
  simp only [V, outer, st', h14, h14t, e, toNat_small (show T < 2 ^ 64 by omega), hd, ht, W]
  omega

end

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

set_option experimental.vcgen true

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- The facts after `positionOf T` at `.LB77` when `rax` is not `-1`: `rax = b`.
set_option hygiene false in
local macro "pos77" : tactic => `(tactic| (
  bbu_norm at hp hag hz hc
  obtain ⟨hb', hs', h14', h15', hax⟩ :=
    post77 hpre hb hS hT1 hp hag rfl rfl hb.rbp rfl h14 rfl rfl
  rw [Kit.z_sub, beq_eq_false_iff_ne] at hz
  obtain ⟨b, hob, hxb⟩ := encOpt_some hax hz
  have hbl := hpn b hob
  have e14 : t'.regs.r14.toBitVec = BitVec.ofNat 64 T := by rw [h14']; exact h14
  have e15 : t'.regs.r15.toBitVec = BitVec.ofNat 64 S.len := by rw [h15']; exact h15
  simp only [CondCode.interp_c, StatusFlags.cf_from_result] at hc
  clear hp hag))

-- `positionOf T`: none goes to `.LB78`; `b < T` to `.LB92`; the same value at `b` and
-- `T` swaps the dests and goes to `.LB68`; else `.LB109`.
theorem lb77 (hpos : Spec "positionOf" positionOfF positionOfA positionOfR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB77") := by
  loop_case
  intro t ht
  have h : At77 s ra t := ht
  obtain ⟨hb, h15, T, h14, hctx, hpd, hst⟩ := h
  obtain ⟨S, hS⟩ : ∃ S, st' s t = S := ⟨_, rfl⟩
  rw [hS] at h15 hctx hpd hst
  obtain ⟨hlp, hnN, hTl, -⟩ := ctx_bounds hctx
  have hn : (env s).n ≤ 1024 := hnN
  have hT1 : T ≤ 1024 := by omega
  have hl : S.len ≤ 1024 := by omega
  have hTn : T < (env s).n := by omega
  -- The facts of the branches, in one form for `kvcgen64`.
  have hpn : ∀ b, positionOf S T = some b → b < S.len := fun _ h => positionOf_some h
  have hpn' : ∀ b, positionOf S T = some b → b ≤ 1024 := fun _ h => by
    have := positionOf_some h; omega
  have herr : ∀ b, positionOf S T = some b → b < T → R0 s = .error .assertion :=
    fun _ h1 h2 => iter_err ⟨S, hctx, hst.trans (bound_lt h1 h2)⟩
  have h109 : ∀ b, positionOf S T = some b → T ≤ b → S.val T ≠ S.val b →
      step (env s) S T = afterPos S T b ((movableCopy S b).getD b) :=
    fun _ h1 h2 h3 => hst.trans (bound_pos h1 h2 h3)
  have h68 : ∀ b, positionOf S T = some b → T ≤ b → S.val T = S.val b →
      InvL (env s) (swapDestinations S T b) (T + 1)
      ∧ loop (env s) (swapDestinations S T b) (T + 1) = R0 s :=
    fun _ h1 h2 h3 => iter_next ⟨S, hctx, hst.trans (bound_eq h1 h2 h3)⟩
  kvcgen64 [hpos]
  all_goals clear hpos
  all_goals try bbu_norm
  case vc1 =>
    rw [hb.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre hb.fm.toMid
  case vc2 => exact Kit.Fm.pre (k := 80) (by decide) hpre hb.fm rfl hb.rsp hb.rbp trivial
  case vc3 =>
    rename_i t' hp hag hz
    bbu_norm at hp hag hz
    obtain ⟨hb', hs', h14', -, hax⟩ :=
      post77 hpre hb hS hT1 hp hag rfl rfl hb.rbp rfl h14 rfl rfl
    rw [Kit.z_sub, beq_iff_eq] at hz
    have e14 : t'.regs.r14.toBitVec = BitVec.ofNat 64 T := by rw [h14']; exact h14
    loop_goto
    · exact stack_mk hb'.rsp
    · exact at78_of (Base.of hb' rfl rfl rfl) e14 hs' hctx hpd hst (encOpt_none hax hz hpn')
    · exact Or.inl (v77_mk hs' hS h14').1
  case vc4 =>
    rename_i t' hp hag hz hc
    pos77
    rw [Kit.cf_sub, hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    loop_goto
    · exact stack_mk hb'.rsp
    · show AtErr s ra _
      exact ⟨Base.of hb' rfl rfl rfl, herr b hob hc⟩
    · exact Or.inl (v77_mk hs' hS h14').2.2
  case vc5 =>
    rename_i t' hp hag hz hc
    pos77
    exact hb'.isSome _ (.inl rfl) (by rw [hxb, toNat_small (by omega), hs']; exact hbl)
  case vc6 =>
    rename_i t' hp hag hz hc
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    exact hb'.isSome _ (.inl rfl) (by rw [e14, toNat_small (by omega), hs']; omega)
  case vc7 =>
    rename_i t' hp hag hz hc hnz
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    obtain ⟨v1, v2, a1, -, -⟩ := slots77 hb' hs' e14 hxb (by omega) hbl hl
    bbu_norm at hnz
    rw [Kit.nz_sub, Bool.not_eq_true', beq_eq_false_iff_ne, v1, v2] at hnz
    loop_goto
    · exact stack_mk hb'.rsp
    · exact at109_of (Base.of hb' rfl rfl rfl) hs' e15 e14 a1 v1 hbl hctx hxb (h109 b hob hc hnz)
    · exact Or.inl (v77_mk hs' hS h14').2.1
  case vc8 =>
    rename_i t' hp hag hz hc hnz
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    obtain ⟨-, -, -, a2, -⟩ := slots77 hb' hs' e14 hxb (by omega) hbl hl
    rw [a2]; exact hb'.fm.dest_isSome (by omega)
  case vc9 =>
    rename_i t' hp hag hz hc hnz
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    obtain ⟨-, -, -, -, a3⟩ := slots77 hb' hs' e14 hxb (by omega) hbl hl
    rw [a3]; exact hb'.fm.dest_isSome (by omega)
  case vc10 =>
    rename_i t' hp hag hz hc hnz
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    obtain ⟨-, -, -, a2, -⟩ := slots77 hb' hs' e14 hxb (by omega) hbl hl
    rw [a2]; exact hb'.fm.dest_isSome (by omega)
  case vc11 =>
    rename_i t' hp hag hz hc hnz
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    obtain ⟨-, -, -, -, a3⟩ := slots77 hb' hs' e14 hxb (by omega) hbl hl
    rw [a3]; exact loadInt_isSome_store _ (hb'.fm.dest_isSome (by omega))
  case vc12 =>
    rename_i t' hp hag hz hc hnz
    pos77
    rw [Kit.cf_sub', hxb, e14, toNat_small (by omega), toNat_small (by omega)] at hc
    obtain ⟨v1, v2, -, a2, a3⟩ := slots77 hb' hs' e14 hxb (by omega) hbl hl
    bbu_norm at hnz
    rw [Kit.nz_sub, Bool.not_eq_false', beq_iff_eq, v1, v2] at hnz
    have sw := swap77 hpre hb' hs' a2 a3 (by omega) hbl
    have hit : InvL (env s) (stOf (mem77 t') (rdi s)) (T + 1)
        ∧ loop (env s) (stOf (mem77 t') (rdi s)) (T + 1) = R0 s := by
      rw [sw.2]; exact h68 b hob hc hnz
    have hpd' : (stOf (mem77 t') (rdi s)).pendingGenerations = S.pendingGenerations := by
      rw [sw.2]; exact (swapDest_shape _ _ _).2.2
    loop_goto
    · exact stack_mk hb'.rsp
    · exact at68_mk sw.1 hb'.rsp hb'.rbp e14 hit
    · exact Or.inl (v68_mk hpd' hS e14 h14 hTn hn)

-- `.LB80` with `b` if `b` is the top, else the search from `len - 1`.
theorem lb109 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB109") := by
  loop_case
  intro t ht
  have h : At109 s ra t := ht
  obtain ⟨T, b, hc, hsi, hst⟩ := h
  have hbl : b < (st' s t).len := hc.2.2.2.2.2.1
  have hl : (st' s t).len ≤ 1024 := hc.bounds.1
  have hx : t.regs.r15.toBitVec - t.regs.rsi.toBitVec = BitVec.ofNat 64 ((st' s t).len - b) := by
    rw [hc.2.1, hsi]; exact sub_of (by omega)
  have hdx : t.regs.r15.toBitVec + -1#64 = BitVec.ofNat 64 ((st' s t).len - 1) := by
    rw [hc.2.1]; exact ofNat_pred (by omega)
  kvcgen64
  all_goals try bbu_norm
  case vc1 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq, hx] at hz
    have h1 : b + 1 = (st' s t).len := by
      have := ofNat_inj64 (by omega) (by omega) hz
      nrm
      omega
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movableCopy_last h1] at hst
      exact at80_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hbl rfl hst
    · simp only [V, outer, st']
      omega
  case vc2 =>
    have hz := (hyp% CondCode.z.interp _ = false)
    bbu_norm at hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hx] at hz
    have h1 : ¬ _ = 1 := fun h1 => hz (congrArg (BitVec.ofNat 64) h1)
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movableCopy_eq hbl] at hst
      exact at83_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hdx (by nrm; omega) (by nrm; omega) hst
    · exact Or.inl (v83_mk rfl rfl (by exact hdx) (by omega))

-- The search at `k`: a movable copy goes to `.LB82` with `k`, else `.LB81`.
theorem lb83 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB83") := by
  loop_case
  intro t ht
  have h : At83 s ra t := ht
  obtain ⟨T, b, k, hc, hsi, hdx, hbk, hkl, hst⟩ := h
  have hl : (st' s t).len ≤ 1024 := hc.bounds.1
  have hxk : t.regs.rdx.toBitVec.toNat = k := by rw [hdx]; exact toNat_small (by omega)
  have hxl : t.regs.rdx.toBitVec.toNat < (st' s t).len := by rw [hxk]; exact hkl
  have hv : rd t.dmem (t.regs.rbp.toBitVec + t.regs.rdx.toBitVec * 8#64 + 64#64)
      = (st' s t).val k := by rw [hc.1.val hxl, hxk]
  have hd : (rd t.dmem (t.regs.rbp.toBitVec + t.regs.rdx.toBitVec * 8#64 + 8256#64)).toNat
      = (st' s t).dest k := by rw [hc.1.dest hxl, hxk]
  have hax : t.regs.rax.toBitVec = (st' s t).val b := hc.2.2.2.2.1
  kvcgen64
  all_goals try bbu_norm
  case vc1 => exact hc.1.isSome _ (.inl rfl) hxl
  case vc3 => exact hc.1.isSome _ (.inr rfl) hxl
  case vc2 =>
    have hz := (hyp% CondCode.nz.interp _ = true)
    bbu_norm at hz
    rw [Kit.nz_sub, Bool.not_eq_true', beq_eq_false_iff_ne, hv, hax] at hz
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movFrom_no hbk (fun h => absurd h.symm hz)] at hst
      exact at81_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hdx hbk hkl hst
    · simp only [V, outer, st']
      omega
  case vc4 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq] at hz
    have hdk : _ = k := hd.symm.trans ((congrArg BitVec.toNat hz).trans hxk)
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movFrom_no hbk (fun _ => hdk)] at hst
      exact at81_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hdx hbk hkl hst
    · simp only [V, outer, st']
      omega
  case vc5 =>
    have hz1 := (hyp% CondCode.nz.interp _ = false)
    have hz := (hyp% CondCode.z.interp _ = false)
    bbu_norm at hz hz1
    rw [Kit.nz_sub, Bool.not_eq_false', beq_iff_eq, hv, hax] at hz1
    rw [Kit.z_sub, beq_eq_false_iff_ne] at hz
    have hdk : _ ≠ k := fun h => hz (BitVec.eq_of_toNat_eq ((hd.trans h).trans hxk.symm))
    rw [movFrom_yes hbk hz1.symm hdk] at hst
    exact at80_mk hc rfl rfl rfl rfl rfl rfl rfl hdx hkl hz1.symm hst
  case vc6 =>
    simp only [V, outer, st']
    omega

-- The search goes to `k - 1`: `.LB82` with `b` at `b`, else `.LB83`.
theorem lb81 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB81") := by
  loop_case
  intro t ht
  have h : At81 s ra t := ht
  obtain ⟨T, b, k, hc, hsi, hdx, hbk, hkl, hst⟩ := h
  have hn := hc.bounds
  have hk1 : t.regs.rdx.toBitVec - 1#64 = BitVec.ofNat 64 (k - 1) := by
    rw [hdx]; exact ofNat_sub1 (by omega)
  kvcgen64
  all_goals try bbu_norm
  case vc1 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq, hsi, hk1] at hz
    have hb : b = k - 1 := ofNat_inj64 (by omega) (by omega) hz
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [← hb, movFrom_self] at hst
      exact at80_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hc.2.2.2.2.2.1 rfl hst
    · simp only [V, outer, st']
      omega
  case vc2 =>
    have hz := (hyp% CondCode.z.interp _ = false)
    bbu_norm at hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hsi, hk1] at hz
    have hb : b ≠ k - 1 := fun h => hz (by rw [h])
    exact at83_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hk1 (by omega)
      (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hkl) hst
  case vc3 =>
    simp only [V, outer, st', hk1, toNat_small (show k - 1 < 2 ^ 64 by omega)]
    rw [hdx, toNat_small (show k < 2 ^ 64 by omega)]
    omega

-- The value at `p` is the value at `b` (`.LB94` is dead).
theorem lb82 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB82") := by
  loop_case
  intro t ht
  have h : At80 s ra t := ht
  obtain ⟨T, b, p, hc, hsi, hp, hvp, hst⟩ := h
  have hl : (st' s t).len ≤ 1024 := hc.bounds.1
  have hxp : t.regs.rsi.toBitVec.toNat = p := by rw [hsi]; exact toNat_small (by omega)
  have hxl : t.regs.rsi.toBitVec.toNat < (st' s t).len := by rw [hxp]; exact hp
  kvcgen64
  all_goals try bbu_norm
  case vc1 => exact hc.1.isSome _ (.inl rfl) hxl
  case vc2 =>
    have hz := (hyp% CondCode.nz.interp _ = true)
    bbu_norm at hz
    rw [Kit.nz_sub, Bool.not_eq_true', beq_eq_false_iff_ne, hc.1.val hxl, hxp, hvp] at hz
    exact absurd hc.2.2.2.2.1 hz
  case vc3 => exact at80_mk hc rfl rfl rfl rfl rfl rfl rfl hsi hp hvp hst
  case vc4 =>
    simp only [V, outer, st']
    omega

-- Swap the dests of `p` and `b`: `.LB95` if `p = T`, `.LB84` if `p` is the top, `.LB110`
-- if `p` is out of reach, else `swapWith p` and `.LB84`.
theorem lb80 (hswap : Spec "swapWith" swapWithF swapWithA swapWithR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB80") := by
  loop_case
  intro t ht
  have h : At80 s ra t := ht
  obtain ⟨T, b, p, hc, hsi, hp, hvp, hst⟩ := h
  obtain ⟨hl, hTl, hTn⟩ := hc.bounds
  have hbl : b < (st' s t).len := hc.2.2.2.2.2.1
  have hn : (env s).n ≤ 1024 := (ctx_bounds hc.2.2.2.2.2.2).2.1
  have hcap := (ctx_bounds hc.2.2.2.2.2.2).2.2.2
  have hp1 : p < 1024 := by omega
  have hb1 : b < 1024 := by omega
  have hxp : t.regs.rsi.toBitVec.toNat = p := by rw [hsi]; exact toNat_small (by omega)
  obtain ⟨e1, e2⟩ := addr80 hc hsi
  have sw := hc.swap80 hpre hsi hp
  have hb0 : Base s ra { t with dmem := mem80 t } := ⟨sw.1, hc.1.rsp, hc.1.rbp⟩
  -- The facts of the branches, in one form for `kvcgen64`.
  obtain ⟨L, hL⟩ : ∃ L, (st' s t).len = L := ⟨_, rfl⟩
  have hMS : MAX_SWAP_DEPTH = 16 := rfl
  have h15 : t.regs.r15.toBitVec = BitVec.ofNat 64 L := hL ▸ hc.2.1
  have hpend : (stOf (mem80 t) (rdi s)).pendingGenerations = (st' s t).pendingGenerations := by
    rw [sw.2]; exact (swapDest_shape _ _ _).2.2
  have hops : (stOf (mem80 t) (rdi s)).trace.length = (st' s t).trace.length := by
    rw [sw.2, (swapDest_shape _ _ _).2.1]
  have hops1 : (stOf (mem80 t) (rdi s)).trace.length ≤ (st' s t).trace.length + 1 := by omega
  have hopsA : (stOf (mem80 t) (rdi s)).trace.length < 6 * (env s).n := by omega
  have htop : p ≠ T → p = L - 1 →
      step (env s) (st' s t) T = placeTop (stOf (mem80 t) (rdi s)) T := fun h1 h2 => by
    rw [sw.2, hst]; exact ap_top h1 (by omega)
  have hfar : p ≠ T → p ≠ L - 1 → MAX_SWAP_DEPTH < L - 1 - p →
      R0 s = .error (.blocked p (L - 1 - p - MAX_SWAP_DEPTH)) := fun h1 h2 h3 => by
    have e := ap_far (st := st' s t) (b := b) h1 (by omega) (by omega)
    rw [hL] at e
    exact iter_err ⟨_, hc.2.2.2.2.2.2, hst.trans e⟩
  have hswp : p ≠ T → p ≠ L - 1 → L - 1 - p ≤ MAX_SWAP_DEPTH →
      step (env s) (st' s t) T = (swapWith (stOf (mem80 t) (rdi s)) p).bind (placeTop · T) :=
    fun h1 h2 h3 => by rw [sw.2, hst]; exact ap_swap h1 (by omega) (by omega)
  have hok : ∀ r, swapWith (stOf (mem80 t) (rdi s)) p = .ok r → p ≠ T → p ≠ L - 1 →
      L - 1 - p ≤ MAX_SWAP_DEPTH → step (env s) (st' s t) T = placeTop r T
        ∧ r.trace.length ≤ (st' s t).trace.length + 1
        ∧ r.pendingGenerations = (st' s t).pendingGenerations :=
    fun r hr h1 h2 h3 => by
      obtain ⟨-, e3, e4⟩ := swapWith_shape hr
      refine ⟨by rw [hswp h1 h2 h3, hr]; rfl, by omega, by rw [e4, hpend]⟩
  have hx1 : t.regs.r15.toBitVec - t.regs.rsi.toBitVec + -1#64 = BitVec.ofNat 64 (L - 1 - p) := by
    rw [h15, hsi, sub_of (by omega), ofNat_pred (by omega)]; congr 1; omega
  have hx17 : MAX_SWAP_DEPTH < L - 1 - p → t.regs.r15.toBitVec - t.regs.rsi.toBitVec - 17#64
      = BitVec.ofNat 64 (L - 1 - p - MAX_SWAP_DEPTH) := fun h3 => by
    rw [h15, hsi, sub_of (by omega), sub_of (L := L - p) (T := 17) (by omega)]
    congr 1; omega
  rw [hL] at hl hp hbl hTl
  kvcgen64 [hswap]
  all_goals clear hswap
  all_goals try bbu_norm
  case vc1 => rw [e1]; exact hc.1.fm.dest_isSome hp1
  case vc2 => rw [e2]; exact hc.1.fm.dest_isSome hb1
  case vc3 => rw [e1]; exact hc.1.fm.dest_isSome hp1
  case vc4 => rw [e2]; exact loadInt_isSome_store _ (hc.1.fm.dest_isSome hb1)
  case vc5 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq, hc.2.2.1, hsi] at hz
    have hTp : T = p := ofNat_inj64 (by omega) (by omega) hz
    subst hTp
    loop_goto
    · exact stack_mk hc.1.rsp
    · exact at95_mk hc sw.1 sw.2 hc.1.rsp hc.1.rbp hsi hst
    · exact Or.inl (v95_mk hpend hsi hc.2.2.1 hTn hn)
  case vc6 =>
    have hz1 := (hyp% CondCode.z.interp _ = false)
    have hz := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz hz1
    rw [Kit.z_sub, beq_eq_false_iff_ne, hc.2.2.1, hsi] at hz1
    rw [Kit.z_sub, beq_iff_eq, h15, hsi, ofNat_pred (by omega)] at hz
    have hpl : L - 1 = p := ofNat_inj64 (by omega) (by omega) hz
    have hpT : p ≠ T := fun e => hz1 (by rw [e])
    loop_goto
    · exact stack_mk hc.1.rsp
    · exact at84_mk sw.1 hc.1.rsp hc.1.rbp hc.2.2.1 hc.2.2.2.2.2.2 (htop hpT hpl.symm) hops1
    · exact Or.inl (v84_mk hpend rfl)
  case vc7 =>
    rename_i hz1 hz2 ha
    bbu_norm at hz1 hz2 ha
    rw [Kit.z_sub, beq_eq_false_iff_ne, hc.2.2.1, hsi] at hz1
    rw [Kit.z_sub, beq_eq_false_iff_ne, h15, hsi, ofNat_pred (by omega)] at hz2
    rw [Kit.a_sub_imm _ 16 (by omega), hx1, toNat_small (by omega), decide_eq_true_eq] at ha
    have hpT : p ≠ T := fun e => hz1 (by rw [e])
    have hpl : p ≠ L - 1 := fun e => hz2 (by rw [e])
    loop_goto
    · exact stack_mk hc.1.rsp
    · exact at110_mk sw.1 hc.1.rsp hc.1.rbp hsi (hx17 (by omega)) (hfar hpT hpl (by omega))
    · exact Or.inl v110_lt
  case vc8 =>
    rw [hc.1.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre sw.1.toMid
  case vc9 =>
    exact swapPre_mk hpre sw.1 hc.1.rsp hc.1.rbp hopsA
  case vc10 =>
    rename_i hz1 hz2 ha t' hp hag af hnz
    bbu_norm at hz1 hz2 ha hp hag hnz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hc.2.2.1, hsi] at hz1
    rw [Kit.z_sub, beq_eq_false_iff_ne, h15, hsi, ofNat_pred (by omega)] at hz2
    rw [Kit.a_sub_imm _ 16 (by omega), hx1, toNat_small (by omega), decide_eq_false_iff_not] at ha
    rw [nz_and, Bool.not_eq_true', beq_eq_false_iff_ne] at hnz
    have hpT : p ≠ T := fun e => hz1 (by rw [e])
    have hpl : p ≠ L - 1 := fun e => hz2 (by rw [e])
    obtain ⟨hb', hg, -⟩ := swap_call_mk hpre sw.1 hc.1.rsp hc.1.rbp hc.1.rbp hp hag
    rw [hxp] at hg
    loop_goto
    · exact stack_of hb'.rsp
    · exact swap_err hb' hc.2.2.2.2.2.2 (hswp hpT hpl (by omega)) hg hnz rfl rfl rfl
    · exact Or.inl v65_lt
  case vc11 =>
    rename_i hz1 hz2 ha t' hp hag af hz
    bbu_norm at hz1 hz2 ha hp hag hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hc.2.2.1, hsi] at hz1
    rw [Kit.z_sub, beq_eq_false_iff_ne, h15, hsi, ofNat_pred (by omega)] at hz2
    rw [Kit.a_sub_imm _ 16 (by omega), hx1, toNat_small (by omega), decide_eq_false_iff_not] at ha
    rw [nz_and, Bool.not_eq_false', beq_iff_eq] at hz
    have hpT : p ≠ T := fun e => hz1 (by rw [e])
    have hpl : p ≠ L - 1 := fun e => hz2 (by rw [e])
    obtain ⟨hb', hg, h14⟩ := swap_call_mk hpre sw.1 hc.1.rsp hc.1.rbp hc.1.rbp hp hag
    rw [hxp] at hg
    obtain ⟨r, hr, -, hr1⟩ := res_ok_of_msb hg
      (by show t'.regs.rax.toBitVec.msb = false; rw [hz]; rfl)
    subst hr1
    obtain ⟨hit, hops', -⟩ := hok _ hr hpT hpl (by omega)
    show At84 s ra _
    exact at84_of (Base.of hb' rfl rfl rfl)
      (by show t'.regs.r14.toBitVec = _; rw [h14]; exact hc.2.2.1)
      hc.2.2.2.2.2.2 hit hops'
  case vc12 =>
    rename_i hz1 hz2 ha t' hp hag af hz
    bbu_norm at hz1 hz2 ha hp hag hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hc.2.2.1, hsi] at hz1
    rw [Kit.z_sub, beq_eq_false_iff_ne, h15, hsi, ofNat_pred (by omega)] at hz2
    rw [Kit.a_sub_imm _ 16 (by omega), hx1, toNat_small (by omega), decide_eq_false_iff_not] at ha
    rw [nz_and, Bool.not_eq_false', beq_iff_eq] at hz
    have hpT : p ≠ T := fun e => hz1 (by rw [e])
    have hpl : p ≠ L - 1 := fun e => hz2 (by rw [e])
    obtain ⟨hb', hg, h14⟩ := swap_call_mk hpre sw.1 hc.1.rsp hc.1.rbp hc.1.rbp hp hag
    rw [hxp] at hg
    obtain ⟨r, hr, -, hr1⟩ := res_ok_of_msb hg
      (by show t'.regs.rax.toBitVec.msb = false; rw [hz]; rfl)
    subst hr1
    obtain ⟨-, -, hpd⟩ := hok _ hr hpT hpl (by omega)
    exact Or.inl (v84_of hpd h14)

end Loop

end Bbu
