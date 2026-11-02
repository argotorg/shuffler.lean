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

theorem planner_resolve_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    VThmWithExit RView RG.Ok resolveAsm resolveA 1182 resolveQ resolveX := by
  letI := L.plannerDecls
  have hclass := vspec_of_body L.planner_classify_decl (planner_classify_correct L X)
  have hadd := addSpec_of_body L.planner_spillSetAdd_decl (X.returnDistinct _)
    (spillSetAdd_unit (L.planner_exit_decl X) (X.outside spillSetAdd_at))
  exact resolve_unit (X.outside resolve_at) hclass hadd

theorem emission_run_vthm [Host] (L : Linked) (X : ExitBoundary) (PM : Addr) (planned : Vector Word MAX_N) :
    letI := L.plannerDecls
    VThmWithExit (RunView PM planned) Sep.G.Ok runAsm (runA planned) runD
      (runQ planned) (runX planned) := by
  letI := L.plannerDecls
  have h := emission_run_correct L X
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨ha, hq, hag⟩ => Or.inl ⟨ha, RunU.post_iff.mpr hq, hag⟩)
      (fun ⟨ha, harg, hx⟩ => Or.inr ⟨ha, harg, RunU.post_iff.mpr hx⟩))
    ((h S PM planned g F s ra).1 t ⟨ht, RunU.pre_iff.mp hp⟩)

theorem planner_run_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    PlannerRunThm := by
  letI := L.plannerDecls
  have hs := planner_helpers_correct L X
  exact plannerRun_unit (L.planner_exit_decl X) (X.outside plannerRun_at) hs.mapInPlace hs.mapClosestCopies hs.mapWildcardSlotCopies
    hs.keepWildcardSlots hs.absorbSurplus
    (fun PM planned => vspecWithExit_of_body L.planner_run_decl (X.returnDistinct _)
      (emission_run_vthm L X PM planned))
    (vspecWithExit_of_body L.planner_resolve_decl (X.returnDistinct _)
      (planner_resolve_correct L X))

theorem planner_run_spec [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    PlannerRunSpec := by
  letI := L.plannerDecls
  exact vspecWithExit_of_body L.planner_plannerRun_decl (X.returnDistinct _)
    (planner_run_correct L X)

end Bbu
