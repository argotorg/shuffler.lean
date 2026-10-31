import BbuKraken.Unit.TopPos

/-!
# `build_bottom_up`: the call block

`.LB.build_bottom_up.15` (`n = 0`: `pend = 0`, `m_plannedMapping`) and `.LB.build_bottom_up.16`: the call of `buildBottomUp`
(`TS.call` with `hloop`) and the branches on the `Status` in `al`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top
set_option experimental.vcgen true

theorem b_15 [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.15" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hn0, hs⟩ := ht
  have hm' := Em.st_pend0 hs.mem
  have h2 := Lc.st_pm hm' (topS s + BitVec.ofNat 64 offPD)
  have hP : (hdr0 s ra).pos = Pm s ra := by
    have := pos_copy (ra := ra) hpre hs.g; rw [hn0] at this; exact this
  kvcgen64
  all_goals try symexec_norm
  case vc1 => rw [hs.sp]; exact Em.isSome_pend hs.mem
  case vc2 => rw [hs.sp]; exact Lc.isSome_pm hm'
  case vc3 =>
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    rw [hs.sp]
    refine ⟨_, TS.cast (hs.step h2 rfl rfl rfl rfl rfl rfl rfl) ?_ rfl⟩
    rw [← hP, show nArg s = 0 from hn0]; rfl
  case vc4 => top_dec

theorem b_16 [Host] [FunDecls] (s ra) (hpre : TopPre s)
    (hloop : Sep.Spec Names.buildBottomUp loopA 2068 loopQ) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.16" →
      Obl s ra blk := by
  simp only [Names.buildBottomUp] at hloop
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, hs⟩ := ht
  kvcgen64 [hloop]
  all_goals try symexec_norm
  refine hs.call hpre (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) fun u st fs hq hal => ?_
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    rename_i hc
    obtain rfl := st_blocked hal hc
    cfg_goto
    · exact hq.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨fs, hq.next rfl rfl rfl rfl rfl rfl rfl rfl⟩
    · top_dec
  case vc2 =>
    rename_i hc1 hc2
    obtain rfl := st_done hal hc1 hc2
    cfg_goto
    · exact hq.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨fs, hq.next rfl rfl rfl rfl rfl rfl rfl rfl⟩
    · top_dec
  case vc3 =>
    rename_i hc1 hc2
    obtain rfl := st_fail hal hc1 hc2
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    exact hq.fail rfl rfl rfl rfl rfl rfl rfl rfl
  case vc4 => top_dec

end Top
end Bbu.Unit
