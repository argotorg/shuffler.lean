import BbuKraken.Unit.Plan.PlannerRunEmissionReady
import BbuKraken.Unit.Plan.PlannerRunBlocked

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem code_blocked_iff (st : Flat.Status) : code st = 1#8 ↔ st = .blocked := by
  cases st <;> decide

set_option maxRecDepth 4096 in
theorem EmitCountLI.blockedBounds {P : Addr} {g : PlannerRunG} {M : Flat.Mapping}
    {F : MProp 64} {s t u : MachineData} {ra : Int64} {lo locals : List Word}
    (h : EmitCountLI P g M F s ra lo locals t) (hok : g.Ok)
    (hm : MapInv g.p.m g.p.n M)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0))
    (a : G)
    (hq : runQ (EmissionLocals.ofList locals h.localLength).planned.pos
      (emissionGhost g hok (localEmissionHdr locals h.localLength)) a t u)
    (hal : al u = 1#8) : BlockedBounds g.p.n (flat a) := by
  obtain ⟨l, _, he, hc⟩ := hq
  have hs := (code_blocked_iff _).mp (hc.symm.trans hal)
  have hr : Flat.emissionRun (EmissionLocals.ofList locals h.localLength).planned.pos l
      (flat (emissionGhost g hok (localEmissionHdr locals h.localLength))) =
      (.blocked, flat a) := Prod.ext hs he.symm
  have hmap : (EmissionLocals.ofList locals h.localLength).planned = M :=
    h.mappingEq h.localLength
  rw [hmap, h.ghost_ctor hok hp] at hr
  exact ctorP_emission_blocked hm _ _ _ _ l hr

end Bbu.Unit.PlannerRunU
