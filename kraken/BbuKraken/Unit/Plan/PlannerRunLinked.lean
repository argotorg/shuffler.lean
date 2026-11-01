module

public import BbuKraken.Unit.Plan.PlannerRunAssemble
import all BbuKraken.Unit.Plan.PlannerRunAssemble
public import BbuKraken.Unit.Plan.ClassifyLinked
import all BbuKraken.Unit.Plan.ClassifyLinked
public import BbuKraken.Unit.Plan.Resolve
import all BbuKraken.Unit.Plan.Resolve
public import BbuKraken.Unit.Run.Linked
import all BbuKraken.Unit.Run.Linked
public import BbuKraken.Unit.SpillAdd
import all BbuKraken.Unit.SpillAdd

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu
open Bbu.Unit

theorem planner_resolve_correct [Host] (L : Linked) :
    letI := L.plannerDecls
    VThm RView RG.Ok resolveAsm resolveA 1182 resolveQ := by
  letI := L.plannerDecls
  have hclass := vspec_of_body L.planner_classify_decl (planner_classify_correct L)
  have hadd := addSpec_of_body L.planner_spillSetAdd_decl spillSetAdd_unit
  exact resolve_unit hclass hadd

theorem emission_run_vthm [Host] (L : Linked) (PM : Addr) (planned : Vector Word MAX_N) :
    letI := L.plannerDecls
    VThm (RunView PM planned) Sep.G.Ok runAsm (runA planned) runD (runQ planned) := by
  letI := L.plannerDecls
  have h := emission_run_correct L
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ ⟨ha, hq, hag⟩ => ⟨ha, RunU.post_iff.mpr hq, hag⟩)
    ((h S PM planned g F s ra).1 t ⟨ht, RunU.pre_iff.mp hp⟩)

theorem planner_run_correct [Host] (L : Linked) :
    letI := L.plannerDecls
    PlannerRunThm := by
  letI := L.plannerDecls
  have hs := planner_helpers_correct L
  exact plannerRun_unit hs.mapInPlace hs.mapClosestCopies hs.mapWildcardSlotCopies
    hs.keepWildcardSlots hs.absorbSurplus
    (fun PM planned => vspec_of_body L.planner_run_decl (emission_run_vthm L PM planned))
    (vspec_of_body L.planner_resolve_decl (planner_resolve_correct L))

theorem planner_run_spec [Host] (L : Linked) :
    letI := L.plannerDecls
    PlannerRunSpec := by
  letI := L.plannerDecls
  exact vspec_of_body L.planner_plannerRun_decl (planner_run_correct L)

end Bbu
