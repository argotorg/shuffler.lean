module

public import BbuKraken.Unit.TopInv
import all BbuKraken.Unit.TopInv

@[expose] public section

/-!
# `build_bottom_up`: the header blocks

The stores of the struct members (`.LB.build_bottom_up.6` for `0 < m`, `.LB.build_bottom_up.19` for `m = 0`) and the loop
`.LB.build_bottom_up.7`: `dest[i] = PD[i]` for `i < m`. `dest_copy`: the copy of `PD[0..m)` gives `Dm`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top
set_option experimental.vcgen true

/-! ## The stores of the members -/

section
variable {S : Addr} {h : Hdr} {R : MProp 64} {m : Mem 64}

-- The first four stores of `.LB.build_bottom_up.6` and `.LB.build_bottom_up.19`. The statement
-- has one flat update of `h`: a nest of seven updates is too large for `isDefEq`.
theorem Em.st_hd4 (hm : (Em S h ∗ R).get m) (a b c d : Word) :
    (Em S { h with tgt := a, n := b, spl := c, data := d } ∗ R).get
      ((((m.storeInt S 8 a.toInt).storeInt (S + 8#64) 8 b.toInt).storeInt (S + 16#64) 8
        c.toInt).storeInt (S + 24#64) 8 d.toInt) :=
  Em.st_data (Em.st_spl (Em.st_n (Em.st_tgt hm a) b) c) d

theorem Em.st_len0 (hm : (Em S h ∗ R).get m) :
    (Em S { h with len := 0#64 } ∗ R).get (m.storeInt (S + 32#64) 8 0) := by
  have := Em.st_len hm 0#64; rwa [BitVec.toInt_zero] at this

-- The last two stores: `ops` and `nops = 0`.
theorem Em.st_on (hm : (Em S h ∗ R).get m) (f : Word) :
    (Em S { h with ops := f, nops := 0#64 } ∗ R).get
      ((m.storeInt (S + 40#64) 8 f.toInt).storeInt (S + 48#64) 8 0) := by
  have := Em.st_nops (Em.st_ops hm f) 0#64; rwa [BitVec.toInt_zero] at this

end

/-! ## The copy of `PD` -/

-- `bindDest` reads `dests` only below `k`.
theorem bindDest_congr {A B : Vector Word MAX_N} (d : Vector Word MAX_N) :
    ∀ k, (∀ p < k, Flat.get A (BitVec.ofNat 64 p) = Flat.get B (BitVec.ofNat 64 p)) →
      Flat.bindDest A k d = Flat.bindDest B k d
  | 0, _ => rfl
  | k + 1, h => by
    rw [Flat.bindDest_succ, Flat.bindDest_succ, bindDest_congr d k fun p hp => h p (by omega),
      h k (by omega)]

theorem get_bindDest (dests d : Vector Word MAX_N) {p : Nat} :
    ∀ k, p < k → k ≤ MAX_N →
      Flat.get (Flat.bindDest dests k d) (BitVec.ofNat 64 p) = Flat.get dests (BitVec.ofNat 64 p)
  | 0, hp, _ => absurd hp (Nat.not_lt_zero _)
  | k + 1, hp, hk => by
    rw [Flat.bindDest_succ, put_ofNat _ (by omega), get_ofNat _ (by omega), get_ofNat _ (by omega),
      Vector.getElem_set]
    split
    · subst ‹k = p›; rw [get_ofNat _ (by omega)]
    · rw [← get_ofNat _ (by omega), get_bindDest dests d k (by omega) (by omega)]

-- The copy of the local `PD` into `dest` is the `dest` of the flat model.
theorem dest_copy {s : MachineData} {ra : Int64} (hg : TopGuard s) :
    Flat.bindDest (locB s ra).pd (mArg s) (hdr0 s ra).dest = Dm s ra :=
  bindDest_congr _ _ fun _ hp =>
    get_bindDest _ _ _ hp (by have := hg.n_le'; have := hg.1; simp only [MAX_N]; omega)

/-! ## The loop `.LB.build_bottom_up.7` -/

theorem one_add_pred {m : Nat} (hm : 0 < m) (hmN : m ≤ MAX_N) :
    1#64 + BitVec.ofNat 64 (m - 1) = BitVec.ofNat 64 m := by
  simp only [MAX_N] at hmN; bv_omega

section
variable {s : MachineData} {ra : Int64} {h : Hdr} {L : Loc} {t : MachineData} {k : Nat}

-- `16480(%rsp,%rdx,8)` and `56(%rsp,%rdx,8)` with `rdx = k`: `PD[k]` and `dest[k]`.
theorem TS.pdx_addr (hs : TS s ra h L t) (hdx : t.regs.rdx.toBitVec = BitVec.ofNat 64 k) :
    t.regs.rsp.toBitVec + t.regs.rdx.toBitVec * 8#64 + 16480#64
      = topS s + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * k) := by
  rw [hs.sp, hdx]; simp only [offPD]; bv_omega

theorem TS.dstx_addr (hs : TS s ra h L t) (hdx : t.regs.rdx.toBitVec = BitVec.ofNat 64 k)
    (hk : k < MAX_N) :
    t.regs.rsp.toBitVec + t.regs.rdx.toBitVec * 8#64 + 56#64 = Fld.mapping_destinationOf (topS s) k := by
  rw [hs.sp, dest_addr, hdx, toNat_ofNat_lt hk]

end

-- `addq $1, rdx; cmpq rax, rdx; jne` with `rdx = k` and `rax = m`.
theorem jne_lt {a r : Word} {k m : Nat} (h : (!1#64 + r - a == BitVec.zero 64) = true)
    (ha : a = BitVec.ofNat 64 m) (hr : r = BitVec.ofNat 64 k) (hk : k < m) : k + 1 < m := by
  subst ha hr
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  have : 1#64 + BitVec.ofNat 64 k - BitVec.ofNat 64 m ≠ 0#64 := h
  bv_omega

theorem jne_eq {a r : Word} {k m : Nat} (h : (!1#64 + r - a == BitVec.zero 64) = false)
    (ha : a = BitVec.ofNat 64 m) (hr : r = BitVec.ofNat 64 k) (hk : k < m) (hm : m ≤ MAX_N) :
    k + 1 = m := by
  subst ha hr
  simp only [Bool.not_eq_false', beq_iff_eq] at h
  have : 1#64 + BitVec.ofNat 64 k - BitVec.ofNat 64 m = 0#64 := h
  simp only [MAX_N] at hm; bv_omega

/-! ## The blocks -/

theorem b_6 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.6" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hm, hs, ha, hax, hdx⟩ := ht
  have hmN : mArg s ≤ MAX_N := by
    have := hs.g.1; have := hs.g.n_le'; simp only [MAX_N]; omega
  have h1 := Em.st_tgt hs.mem t.regs.rcx.toBitVec
  have h2 := Em.st_n h1 t.regs.rsi.toBitVec
  have h3 := Em.st_spl h2 t.regs.r9.toBitVec
  have h4 := Em.st_hd4 hs.mem t.regs.rcx.toBitVec t.regs.rsi.toBitVec t.regs.r9.toBitVec
    t.regs.r10.toBitVec
  have h5 := Em.st_len h4 t.regs.rdx.toBitVec
  have hops := rd_ops h5
  unfold rd at hops; simp only [offOps] at hops
  have h7 := Em.st_on h5 (opsArg s)
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try rw [hs.sp]
  case vc1 => exact Em.isSome_tgt hs.mem
  case vc2 => exact Em.isSome_hd h1 (by simp)
  case vc3 => exact Em.isSome_hd h2 (by simp)
  case vc4 => exact Em.isSome_hd h3 (by simp)
  case vc5 => exact Em.isSome_hd h4 (by simp)
  case vc6 => exact isSome_ops h5 hpre hs.g
  case vc7 => exact Em.isSome_hd h5 (by simp)
  case vc8 => rw [hops]; exact Em.isSome_hd (Em.st_ops h5 _) (by simp)
  case vc9 =>
    rw [hops]
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    have hdi : BitVec.ofNat 64 (mArg s) = s.regs.rdi.toBitVec := by
      simp only [mArg, rdi, Reg64s.get64_rdi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨0, hm, TS.cast (hs.step h7 rfl rfl rfl rfl rfl rfl rfl) ?_ rfl, ha.rsi, ?_, rfl⟩
    · unfold hdr; rw [ha.rcx, ha.rsi, ha.r9, ha.r10, hdx, hdi]; rfl
    · rw [hax]; exact one_add_pred hm hmN
  case vc10 => top_dec

theorem b_19 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.19" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hm0, hs, ha⟩ := ht
  have h1 := Em.st_tgt hs.mem t.regs.rcx.toBitVec
  have h2 := Em.st_n h1 t.regs.rsi.toBitVec
  have h3 := Em.st_spl h2 t.regs.r9.toBitVec
  have h4 := Em.st_hd4 hs.mem t.regs.rcx.toBitVec t.regs.rsi.toBitVec t.regs.r9.toBitVec
    t.regs.r10.toBitVec
  have h5 := Em.st_len0 h4
  have hops := rd_ops h5
  unfold rd at hops; simp only [offOps] at hops
  have h7 := Em.st_on h5 (opsArg s)
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals rw [hs.sp]
  case vc1 => exact Em.isSome_tgt hs.mem
  case vc2 => exact Em.isSome_hd h1 (by simp)
  case vc3 => exact Em.isSome_hd h2 (by simp)
  case vc4 => exact Em.isSome_hd h3 (by simp)
  case vc5 => exact Em.isSome_hd h4 (by simp)
  case vc6 => exact isSome_ops h5 hpre hs.g
  case vc7 => exact Em.isSome_hd h5 (by simp)
  case vc8 => rw [hops]; exact Em.isSome_hd (Em.st_ops h5 _) (by simp)
  case vc9 =>
    rw [hops]
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      have hdi : s.regs.rdi.toBitVec = 0#64 := by
        simp only [Reg64s.get64_rdi] at hm0; bv_omega
      refine ⟨TS.cast (hs.step h7 rfl rfl rfl rfl rfl rfl rfl) ?_ rfl, ha.rsi⟩
      unfold hdr; rw [Dm_m0 s ra hm0, ha.rcx, ha.rsi, ha.r9, ha.r10, hdi]; rfl
    · top_dec

theorem b_7 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.7" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨i, hi, hs, hsi, hax, hdx⟩ := ht
  have hiN := hs.m_lt hi
  have hmN : mArg s ≤ MAX_N := by
    have := hs.g.1; have := hs.g.n_le'; simp only [MAX_N]; omega
  have hpa := hs.pdx_addr hdx
  have hda := hs.dstx_addr hdx hiN
  have hrd : rd t.dmem (t.regs.rsp.toBitVec + t.regs.rdx.toBitVec * 8#64 + 16480#64)
      = (locB s ra).pd[i] := by
    rw [hpa]; exact Lc.rd_pd hs.mem hiN
  unfold rd at hrd
  have hm' := Em.st_dest hs.mem hiN (locB s ra).pd[i]
  rw [← hda] at hm'
  have hpd : (Flat.bindDest (locB s ra).pd i (hdr0 s ra).dest).set i (locB s ra).pd[i]
      = Flat.bindDest (locB s ra).pd (i + 1) (hdr0 s ra).dest := by
    rw [Flat.bindDest_succ, put_ofNat _ hiN, get_ofNat _ hiN]
  have hd1 : 1#64 + t.regs.rdx.toBitVec = BitVec.ofNat 64 (i + 1) := by
    rw [hdx]; simp only [MAX_N] at hiN; bv_omega
  kvcgen64
  all_goals try symexec_norm
  case vc1 => rw [hpa]; exact Lc.isSome_pd hs.mem hiN
  case vc2 => rw [hda]; exact Em.isSome_dest hs.mem hiN
  case vc3 =>
    rename_i hc
    have hk1 := jne_lt hc hax hdx hi
    rw [hrd]
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨i + 1, hk1, TS.cast (hs.step hm' rfl rfl rfl rfl rfl rfl rfl) (by rw [← hpd]; rfl) rfl,
        hsi, hax, hd1⟩
    · have e1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := toNat_ofNat_lt (by omega)
      have e2 : t.regs.rdx.toBitVec.toNat = i := by rw [hdx]; exact toNat_ofNat_lt hiN
      top_dec
      rw [hd1, e1, e2]; omega
  case vc4 =>
    rename_i hc
    have he := jne_eq hc hax hdx hi hmN
    have hD : Flat.bindDest (locB s ra).pd (i + 1) (hdr0 s ra).dest = Dm s ra := by
      rw [he]; exact dest_copy hs.g
    rw [hrd]
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    exact ⟨TS.cast (hs.step hm' rfl rfl rfl rfl rfl rfl rfl) (by rw [← hD, ← hpd]; rfl) rfl, hsi⟩
  case vc5 => top_dec

end Top
end Bbu.Unit
