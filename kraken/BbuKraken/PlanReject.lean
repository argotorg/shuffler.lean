import BbuKraken.Unit.Plan.EntryRejectIds
import BbuKraken.Bin
import BbuKraken.PlannerLink

namespace Bbu
open Bbu.Unit

/-- Invalid sizes or enum bytes need no input or output arrays. -/
theorem plan_rejects_bad_args [Host] [FunDecls] (a b : BitVec 32) (F : MProp 64) :
    Sep.Body planAsm (EntryU.RejectPre a b F) (EntryU.RejectPost a b F) :=
  EntryU.plan_rejects_bad_args a b F

/-- Invalid IDs need only the source and target prefixes visited before rejection. -/
theorem plan_rejects_invalid_ids [Host] [FunDecls]
    (g : EntryRejectIds.G) (F : MProp 64) :
    Sep.Body planAsm (EntryRejectIds.Pre g F) (EntryRejectIds.Post g F) :=
  EntryRejectIds.plan_rejects_invalid_ids g F

theorem plan_harness_rejects_bad_args (a b : BitVec 32) (F : MProp 64) :
    letI := binLinked.plannerDecls
    Sep.Body planAsm (EntryU.RejectPre a b F) (EntryU.RejectPost a b F) := by
  letI := binLinked.plannerDecls
  exact plan_rejects_bad_args a b F

theorem plan_harness_rejects_invalid_ids (g : EntryRejectIds.G) (F : MProp 64) :
    letI := binLinked.plannerDecls
    Sep.Body planAsm (EntryRejectIds.Pre g F) (EntryRejectIds.Post g F) := by
  letI := binLinked.plannerDecls
  exact plan_rejects_invalid_ids g F

end Bbu
