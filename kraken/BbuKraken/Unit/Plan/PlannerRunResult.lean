module

public import BbuKraken.Unit.Plan.PlannerRunMem
import all BbuKraken.Unit.Plan.PlannerRunMem
public import BbuKraken.Unit.Plan.PlannerRunModel
import all BbuKraken.Unit.Plan.PlannerRunModel

@[expose] public section

namespace Bbu.Unit.PlannerRunU

def emptyRunU : Flat.RunU :=
  let w : Vector Word MAX_N := Vector.replicate MAX_N 0#64
  ⟨⟨w, w⟩, ⟨w, w, 0#64, 0#64⟩, ⟨w, w, w⟩,
    ⟨Vector.replicate MAX_N 0#8, w⟩⟩

theorem plannerRunQ_bad_target (g : PlannerRunG) (s t : MachineData)
    (h : Flat.targetsFrom g.p.fl g.spills 0 = false) (hal : al t = 2#8) :
    plannerRunQ g (withSaw g 0#8) s t := by
  refine ⟨fun _ => emptyRunU, ?_⟩
  rw [plannerRun_bad_target _ _ _ _ h]
  exact ⟨hal, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem plannerRunX_bad_target (g : PlannerRunG) (s t : MachineData)
    (h : Flat.targetsFrom g.p.fl g.spills 0 = false) :
    plannerRunX g (withSaw g 0#8) s t := by
  refine ⟨fun _ => emptyRunU, ?_⟩
  rw [plannerRun_bad_target _ _ _ _ h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Bbu.Unit.PlannerRunU
