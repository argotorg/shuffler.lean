import BbuKraken.Unit.Plan.EntryRejectIdsStart
import BbuKraken.Unit.Plan.EntryRejectIdsRead
import BbuKraken.Unit.Plan.EntryRejectIdsAdvance

open Std.WP Lean.Order ProofKit
open scoped Program.WP

namespace Bbu.Unit.EntryRejectIds
open Bbu.Sep

/-- ID rejection needs the scan prefixes and the entry frame, with no output buffers. -/
theorem plan_rejects_invalid_ids [Host] [FunDecls] (g : G) (F : MProp 64) :
    Sep.Body planAsm (Pre g F) (Post g F) := by
  intro s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst t
  refine Program.WP.cfg (Inv g F s ra) (V g) ?_ rfl
  refine forallBlocks_cases EntryU.labels EntryU.labels_cover fun l hl => ?_
  simp only [EntryU.labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry g F s ra
  · exact b_fn g F s ra hp
  · exact b_0 g F s ra hp.1
  · exact b_1 g F s ra hp.1
  · exact b_2 g F s ra hp.1
  · exact b_3 g F s ra hp.1
  · exact b_4 g F s ra hp.1
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · exact b_9 g F s ra
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · cfg_block [Obl]
    intro t ht
    simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  · exact b_14 g F s ra hp.1

end Bbu.Unit.EntryRejectIds
