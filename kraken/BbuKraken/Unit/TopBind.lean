module

public import BbuKraken.Unit.TopInv
import all BbuKraken.Unit.TopInv

@[expose] public section

/-!
# `build_bottom_up`: the bind blocks

The loop `.LB.build_bottom_up.5`/`.LB.build_bottom_up.4`: `PD[k] = dest[k]` and `PP[dest[k]] = k` for `k < m` (`locK`), with its
entry `.LB.build_bottom_up.3`. `dest[k] < n` (`dest_lt`), so the branch `dest[k] = -1` is dead.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top
set_option experimental.vcgen true

section
variable {s : MachineData} {ra : Int64} {h : Hdr} {L : Loc} {t : MachineData} {k : Nat}

-- `24672(%rsp,%rdx,8)` with `rdx = d`: `PP[d]`.
theorem TS.ppd_addr (hs : TS s ra h L t) (d : Word) :
    t.regs.rsp.toBitVec + d * 8#64 + 24672#64
      = topS s + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * d.toNat) := by
  rw [hs.sp]; simp only [offPP]; bv_omega

theorem locK_succ (hk : k < MAX_N) (hd : (Flat.get (flatDest s) (BitVec.ofNat 64 k)).toNat < MAX_N) :
    locK s ra (k + 1) =
      { { locK s ra k with pd := (locK s ra k).pd.set k (Flat.get (flatDest s) (BitVec.ofNat 64 k)) } with
        pp := (locK s ra k).pp.set _ (BitVec.ofNat 64 k) hd } := by
  simp only [locK, Flat.bindDest_succ, Flat.bindPos_succ, put_ofNat _ hk, Flat.put_of_lt _ hd]

end

-- `leaq 1(rax), rdx; cmpq rdx, rdi; je` with `rax = k`.
theorem succ_eq_of_cmp {a b r : Word} {k : Nat} (h : (a - (r + 1#64) == BitVec.zero 64) = true)
    (ha : a = b) (hr : r = BitVec.ofNat 64 k) (hk : k < b.toNat) : k + 1 = b.toNat := by
  subst ha hr
  simp only [beq_iff_eq] at h
  have : a - (BitVec.ofNat 64 k + 1#64) = 0#64 := h
  bv_omega

theorem succ_lt_of_cmp {a b r : Word} {k : Nat} (h : (a - (r + 1#64) == BitVec.zero 64) = false)
    (ha : a = b) (hr : r = BitVec.ofNat 64 k) (hk : k < b.toNat) : k + 1 < b.toNat := by
  subst ha hr
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  have : a - (BitVec.ofNat 64 k + 1#64) ≠ 0#64 := h
  bv_omega

theorem add_one_ofNat {r : Word} {k : Nat} (hr : r = BitVec.ofNat 64 k) :
    r + 1#64 = BitVec.ofNat 64 (k + 1) := by
  subst hr; bv_omega

theorem b_3 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.3" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hm, hs, ha⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.build_bottom_up.5" =>
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨0, hm, hs.next rfl rfl rfl rfl rfl rfl rfl rfl, ha.next rfl rfl rfl rfl rfl rfl, rfl⟩
    · top_dec

theorem b_5 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.5" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨k, hk, hs, ha, hax⟩ := ht
  have hkN := hs.m_lt hk
  have hrd := hs.rd_dst ha hpre hax hk
  unfold rd at hrd
  have hdl := dest_lt hpre hs.g hk
  have hnN := hs.g.n_le'
  have hdN : (Flat.get (flatDest s) (BitVec.ofNat 64 k)).toNat < MAX_N := by simp only [MAX_N]; omega
  kvcgen64
  -- `all_goals try exact` on these goals hits the maximum recursion depth: each goal gets its own
  -- tactic.
  all_goals try symexec_norm at ⊢
  case vc1 => exact hs.isSome_dst ha hpre hax hk
  case vc3 => exact hs.isSome_pdk hax hkN
  case vc2 =>
    -- `je .LB.build_bottom_up.4`: `dest[k] = -1`, against `dest_lt`.
    rename_i hc; symexec_norm at hc; rw [hrd] at hc
    have he : Flat.get (flatDest s) (BitVec.ofNat 64 k) = Flat.NONE :=
      none_of_jne (by simpa only [Bool.not_eq_false'] using hc)
    have h1 : Flat.NONE.toNat = 18446744073709551615 := by decide
    rw [he, h1] at hdl; omega
  case vc4 =>
    rw [hrd, hs.ppd_addr]; exact Lc.isSome_pp (hs.st_pdk hax hkN _) hdN
  case vc5 =>
    rw [hrd]
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      have hm := Lc.st_pp (hs.st_pdk hax hkN (Flat.get (flatDest s) (BitVec.ofNat 64 k))) hdN
        t.regs.rax.toBitVec
      rw [← hs.ppd_addr] at hm
      exact ⟨k, hk, TS.cast (hs.step hm rfl rfl rfl rfl rfl rfl rfl) rfl
        (by rw [locK_succ hkN hdN, hax]), ha.next rfl rfl rfl rfl rfl rfl, hax⟩
    · top_dec

theorem b_4 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.4" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨k, hk, hs, ha, hax⟩ := ht
  have hkN := hs.m_lt hk
  have hdi := congrArg (·.toBitVec) ha.rdi
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.build_bottom_up.6" =>
    rename_i hc
    have he : k + 1 = mArg s := succ_eq_of_cmp hc hdi hax hk
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      refine ⟨by omega, TS.cast (hs.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl (by rw [he, locK_m]),
        ha.next rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
      · rw [hax]; congr 1; omega
      · rw [add_one_ofNat hax, he]
    · top_dec
  | other =>
    rename_i hc
    have hk1 := succ_lt_of_cmp hc hdi hax hk
    first
      | (simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
         exact ⟨k + 1, hk1, hs.next rfl rfl rfl rfl rfl rfl rfl rfl,
           ha.next rfl rfl rfl rfl rfl rfl, add_one_ofNat hax⟩)
      | (top_dec
         rw [add_one_ofNat hax, hax, toNat_ofNat_lt hkN, toNat_ofNat_lt (hs.m_lt hk1)]
         omega)

end Top
end Bbu.Unit
