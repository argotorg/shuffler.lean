module

public import FlatShuffler.Unit.Run
import all FlatShuffler.Unit.Run
public import FlatShuffler.PlannerLink
import all FlatShuffler.PlannerLink
public import FlatShuffler.Unit.Push
import all FlatShuffler.Unit.Push
public import FlatShuffler.Unit.Dup
import all FlatShuffler.Unit.Dup
public import FlatShuffler.Unit.SwapWith
import all FlatShuffler.Unit.SwapWith
public import FlatShuffler.Unit.Produce
import all FlatShuffler.Unit.Produce
public import FlatShuffler.Unit.Generate
import all FlatShuffler.Unit.Generate
public import FlatShuffler.Unit.Permute
import all FlatShuffler.Unit.Permute
public import FlatShuffler.Unit.Lowest
import all FlatShuffler.Unit.Lowest
public import FlatShuffler.Unit.Loop
import all FlatShuffler.Unit.Loop

@[expose] public section

/-! The `run` callees all come from assembly unit proofs in the planner function table. -/

namespace FlatShuffler
open FlatShuffler.Unit

theorem emission_run_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    RunThm runAsm := by
  letI := L.plannerDecls
  have hexit := L.planner_exit_decl X
  have hspill := Sep.spec_of_body L.planner_isSpilled_decl isSpilled_unit
  have hcopy := Sep.spec_of_body L.planner_shallowestCopyPosition_decl shallowestCopy_unit
  have hpush := Sep.specWithExit_of_body L.planner_push_decl (X.returnDistinct _)
    (push_unit hexit (X.outside push_at))
  have hdup := Sep.specWithExit_of_body L.planner_dup_decl (X.returnDistinct _)
    (dup_unit hexit (X.outside dup_at))
  have hswap := Sep.specWithExit_of_body L.planner_swapWith_decl (X.returnDistinct _)
    (swapWith_unit hexit (X.outside swapWith_at))
  have hpop := Sep.specWithExit_of_body L.planner_pop_decl (X.returnDistinct _)
    (pop_unit hexit (X.outside pop_at))
  have hprod := Sep.specWithExit_of_body L.planner_produce_decl (X.returnDistinct _)
    (produce_unit hexit (X.outside produce_at) hcopy hspill hpush hdup)
  have hgen := Sep.specWithExit_of_body L.planner_generate_decl (X.returnDistinct _)
    (generate_unit hexit (X.outside generate_at) hprod hswap)
  have hperm := fun p => Sep.specWithExit_of_bodyW L.planner_permute_decl (X.returnDistinct _)
    (permute_unit hexit (X.outside finish_at) hcopy p)
  have hsur := Sep.specWithExit_of_body L.planner_removeSurplus_decl (X.returnDistinct _)
    (removeSurplus_unit hexit (X.outside removeSurplus_at) hswap hpop)
  have hav := Sep.spec_of_body L.planner_isAvailable_decl (isAvailable_unit hspill hcopy)
  have hloop := Sep.specWithExit_of_body L.planner_buildBottomUp_decl (X.returnDistinct _)
    (loop_unit hexit (X.outside loop_at) hperm hspill hcopy hgen hswap)
  have hlow := permuteAtLowestHeight_unit hexit (X.outside permuteAtLowestHeight_at) hperm
  exact run_unit hexit (X.outside run_at) hsur
    (fun PM planned => vspecWithExit_of_body L.planner_permuteAtLowestHeight_decl
      (X.returnDistinct _) (RunU.lowest_vthm hlow PM planned)) hav hloop

end FlatShuffler
