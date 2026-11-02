module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionReady
import all FlatShuffler.Unit.Plan.PlannerRunEmissionReady
public import FlatShuffler.Unit.Plan.PlannerRunBlocked
import all FlatShuffler.Unit.Plan.PlannerRunBlocked

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

theorem code_blocked_iff (st : Flat.EmissionOutcome) : code st = some 1#8 ↔ st = .blocked := by
  cases st with
  | returned status => cases status <;> decide
  | assertionExit => decide

set_option maxRecDepth 4096 in
theorem EmitCountLI.blockedBounds {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping}
    {F : MProp 64} {s t u : MachineData} {ra : Int64} {lo locals : List Word}
    (h : EmitCountLI P g M F s ra lo locals t) (hok : g.Ok)
    (hm : MapInv g.p.sourceSize g.p.targetSize M)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0))
    (a : G)
    (hq : runQ (EmissionLocals.ofList locals h.localLength).planned.pos
      (emissionGhost g hok (localEmissionHdr locals h.localLength)) a t u)
    (hal : al u = 1#8) : BlockedBounds g.p.targetSize (flat a) := by
  obtain ⟨l, _, he, hc⟩ := hq
  have hs := (code_blocked_iff _).mp (hc.symm.trans (congrArg some hal))
  have hr : Flat.emissionRun (EmissionLocals.ofList locals h.localLength).planned.pos l
      (flat (emissionGhost g hok (localEmissionHdr locals h.localLength))) =
      (.blocked, flat a) := Prod.ext hs he.symm
  have hmap : (EmissionLocals.ofList locals h.localLength).planned = M :=
    h.mappingEq h.localLength
  rw [hmap, h.ghost_ctor hok hp] at hr
  exact ctorP_emission_blocked hm _ _ _ _ l hr

end FlatShuffler.Unit.PlannerRunU
