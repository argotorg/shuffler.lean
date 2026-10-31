import BbuKraken.Unit.Run
import BbuKraken.PlannerLink
import BbuKraken.Unit.Push
import BbuKraken.Unit.Dup
import BbuKraken.Unit.SwapWith
import BbuKraken.Unit.Produce
import BbuKraken.Unit.Generate
import BbuKraken.Unit.Permute
import BbuKraken.Unit.Lowest
import BbuKraken.Unit.Loop

/-! The `run` callees all come from assembly unit proofs in the planner function table. -/

namespace Bbu
open Bbu.Unit

theorem emission_run_correct [Host] (L : Linked) :
    letI := L.plannerDecls
    RunThm runAsm := by
  letI := L.plannerDecls
  have hspill := Sep.spec_of_body L.planner_isSpilled_decl isSpilled_unit
  have hcopy := Sep.spec_of_body L.planner_shallowestCopyPosition_decl shallowestCopy_unit
  have hpush := Sep.spec_of_body L.planner_push_decl push_unit
  have hdup := Sep.spec_of_body L.planner_dup_decl dup_unit
  have hswap := Sep.spec_of_body L.planner_swapWith_decl swapWith_unit
  have hpop := Sep.spec_of_body L.planner_pop_decl pop_unit
  have hprod := Sep.spec_of_body L.planner_produce_decl (produce_unit hcopy hspill hpush hdup)
  have hgen := Sep.spec_of_body L.planner_generate_decl (generate_unit hprod hswap)
  have hperm := fun p => Sep.spec_of_bodyW L.planner_permute_decl (permute_unit hcopy p)
  have hsur := Sep.spec_of_body L.planner_removeSurplus_decl (removeSurplus_unit hswap hpop)
  have hav := Sep.spec_of_body L.planner_isAvailable_decl (isAvailable_unit hspill hcopy)
  have hloop := Sep.spec_of_body L.planner_buildBottomUp_decl
    (loop_unit hperm hspill hcopy hgen hswap)
  have hlow := permuteAtLowestHeight_unit hperm
  exact run_unit hsur
    (fun PM planned => vspec_of_body L.planner_permuteAtLowestHeight_decl
      (RunU.lowest_vthm hlow PM planned)) hav hloop

end Bbu
