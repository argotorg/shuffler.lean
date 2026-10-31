import BbuKraken.Unit.TopInv

/-!
# `build_bottom_up`: the exit blocks

`.LB.build_bottom_up.12` (`Done`) and `.LB.build_bottom_up.13` (`Blocked`): the stores to `blocked`; `.LB.build_bottom_up.14` (the guard
fails, `ret` with `-2`, `trFail`) and `.LB.build_bottom_up.17` (`addq $32872`, `ret`, `TR.ret_17`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top
set_option experimental.vcgen true

theorem b_12 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.12" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨fs, hq⟩ := ht
  have hb : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 32888#64) 8).get! = blkArg s :=
    hq.blk
  kvcgen64
  all_goals try symexec_norm
  case vc1 => exact hq.isSome_blkp hpre
  case vc2 => rw [hb]; exact hq.blkm.loadInt_isSome in_blk0
  case vc3 => rw [hb]; exact (hq.blkm.storeInt _ _ _).loadInt_isSome in_blk1
  case vc4 => exact hq.isSome_fr ((hq.mapped.storeInt _ _ _).storeInt _ _ _) 48
  case vc5 =>
    cfg_goto
    · exact hq.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      rw [hb]
      exact hq.store hpre (x := 0#64) (y := 0#64) (by rfl) rfl (topRes_done hq.g hq.res)
        ⟨rfl, rfl, rfl⟩ (by rfl) (by rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    · top_dec

theorem b_13 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.13" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨fs, hq⟩ := ht
  have hb : BitVec.ofInt 64 (Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 32888#64) 8).get! = blkArg s :=
    hq.blk
  kvcgen64
  all_goals try symexec_norm
  case vc1 => exact hq.isSome_fr hq.mapped 16448
  case vc2 => exact hq.isSome_blkp hpre
  case vc3 => rw [hb]; exact hq.blkm.loadInt_isSome in_blk0
  case vc4 => exact hq.isSome_fr (hq.mapped.storeInt _ _ _) 16456
  case vc5 => rw [hb]; exact (hq.blkm.storeInt _ _ _).loadInt_isSome in_blk1
  case vc6 => exact hq.isSome_fr ((hq.mapped.storeInt _ _ _).storeInt _ _ _) 48
  case vc7 =>
    cfg_goto
    · exact hq.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      rw [hb, hq.rd_off, hq.rd_exc1 hpre (a := rd s.dmem (s.regs.rsp.toBitVec + 8#64)) rfl]
      exact hq.store hpre rfl rfl (topRes_blocked hq.g hq.res) ⟨rfl, rfl, rfl⟩ rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl
    · top_dec

theorem b_14 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.14" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hd, hsp, e1, e2, e3, e4, e5, e6, hg⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  all_goals first
    | (apply TR.ret; exact trFail hpre hg hd hsp e1 e2 e3 e4 e5 e6 rfl)
    | (apply TR.isSome; exact trFail hpre hg hd hsp e1 e2 e3 e4 e5 e6 rfl)

theorem b_17 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.17" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  kvcgen64
  all_goals try symexec_norm
  all_goals first
    | (apply TR.ret; exact ht.ret_17 rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    | (apply TR.isSome; exact ht.ret_17 rfl rfl rfl rfl rfl rfl rfl rfl rfl)

end Top
end Bbu.Unit
