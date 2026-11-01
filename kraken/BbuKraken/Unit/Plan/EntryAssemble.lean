module

public import BbuKraken.Unit.Plan.EntryCfgStart
import all BbuKraken.Unit.Plan.EntryCfgStart
public import BbuKraken.Unit.Plan.EntryCfgScan
import all BbuKraken.Unit.Plan.EntryCfgScan
public import BbuKraken.Unit.Plan.EntryCfgClear
import all BbuKraken.Unit.Plan.EntryCfgClear
public import BbuKraken.Unit.Plan.EntryCfgFinish
import all BbuKraken.Unit.Plan.EntryCfgFinish
public import BbuKraken.Unit.Plan.EntryRejectFull
import all BbuKraken.Unit.Plan.EntryRejectFull

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

set_option maxRecDepth 16384 in
theorem plan_valid_unit [Host] [FunDecls] (g : EG) (F : MProp 64)
    (hs : Sizes g) (hrun : PlannerRunSpec) :
    Sep.Body planAsm (Pre g F) (Post g F) := by
  intro s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst t
  refine Program.WP.cfg (EntryInv g F s ra) (entryV g) ?_ rfl
  refine forallBlocks_cases EntryU.labels EntryU.labels_cover fun l hl => ?_
  simp only [EntryU.labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cfg_entry g F s ra
  · exact cfg_fn g F s ra hp hs
  · exact cfg_0 g F s ra hp.1 hs
  · exact cfg_1 g F s ra hp.1 hs
  · exact cfg_2 g F s ra hp.1 hs
  · exact cfg_3 g F s ra hp.1 hs
  · exact cfg_4 g F s ra hp.1 hs
  · exact cfg_5 g F s ra
  · exact cfg_6 g F s ra hs
  · exact cfg_7 g F s ra hs
  · exact cfg_8 g F s ra hp hs hrun
  · exact cfg_9 g F s ra
  · exact cfg_10 g F s ra
  · exact cfg_11 g F s ra
  · cfg_block [EntryObl]
    intro t ht
    simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [EntryObl]
    intro t ht
    simp only [EntryInv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · exact cfg_14 g F s ra hp.1 hs

theorem plan_unit [Host] [FunDecls] (hrun : PlannerRunSpec) (g : EG) (F : MProp 64) :
    Sep.Body planAsm (Pre g F) (Post g F) := by
  by_cases hs : Sizes g
  · exact plan_valid_unit g F hs hrun
  · intro s ra
    refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
    exact ((plan_reject_full g F) s ra).1 t ⟨ht, hp, hs⟩

end Bbu.Unit.EntryValidU
