module

public import FlatShuffler.Unit.Plan.PlannerRunMem
import all FlatShuffler.Unit.Plan.PlannerRunMem
public import FlatShuffler.Unit.Plan.PlannerRunModel
import all FlatShuffler.Unit.Plan.PlannerRunModel

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU

def emptyRunU : Flat.RunU :=
  let w : Vector Word maxStackSize := Vector.replicate maxStackSize 0#64
  ⟨⟨w, w⟩, ⟨w, w, 0#64, 0#64⟩, ⟨w, w, w⟩,
    ⟨Vector.replicate maxStackSize 0#8, w⟩⟩

theorem plannerRunX_bad_target (g : PlannerCallMemory) (s t : MachineData)
    (h : Flat.targetsFrom g.p.fl g.spills 0 = false) :
    plannerRunX g (withSaw g 0#8) s t := by
  refine ⟨fun _ => emptyRunU, ?_⟩
  rw [plannerRun_bad_target _ _ _ _ h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FlatShuffler.Unit.PlannerRunU
