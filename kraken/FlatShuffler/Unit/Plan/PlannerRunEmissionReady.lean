module

public import FlatShuffler.Unit.Plan.PlannerRunEmissionModel
import all FlatShuffler.Unit.Plan.PlannerRunEmissionModel
public import FlatShuffler.Unit.Plan.PlannerRunEmissionView
import all FlatShuffler.Unit.Plan.PlannerRunEmissionView

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

section
variable {P : Addr} {g : PlannerCallMemory} {M : Flat.Mapping} {F : MProp 64}
    {s t : MachineData} {ra : Int64} {lo locals : List Word}

theorem EmitCountLI.hdr_fixed (h : EmitCountLI P g M F s ra lo locals t) :
    emissionHdr g (localEmissionHdr locals h.localLength) =
      localEmissionHdr locals h.localLength := by
  obtain ⟨ht, hn, hs, hd, _, ho, _⟩ := h.header.localHdr h.localLength
  unfold emissionHdr
  rw [← ht, ← hn, ← hs, ← hd, ← ho]

theorem EmitCountLI.ghost_ctor (h : EmitCountLI P g M F s ra lo locals t)
    (hok : g.Ok)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0)) :
    let a := localEmissionHdr locals h.localLength
    flat (emissionGhost g hok a) =
      Flat.ctorP (vec ((g.data.toList.take g.dataCapacity).map StackSlot.ofWord))
        g.p.m g.p.fl.target g.p.n M g.spills
        ⟨a.dest, a.pos, a.blkOff, a.blkExc⟩ := by
  obtain ⟨_, _, _, _, hlen, _, hnops⟩ := h.header.localHdr h.localLength
  dsimp only
  rw [emissionGhost_flat, hlen, hnops]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, List.take_zero, List.map_nil]
  rw [ctorP_data _ (g.data.map StackSlot.ofWord), h.ctorP hok hp]
  rfl

theorem EmitCountLI.ghost_ctor_full (h : EmitCountLI P g M F s ra lo locals t)
    (hok : g.Ok)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0)) :
    let a := localEmissionHdr locals h.localLength
    Flat.restoreData g.dataCapacity (g.data.map StackSlot.ofWord)
      (flat (emissionGhost g hok a)) =
      Flat.ctorP (g.data.map StackSlot.ofWord) g.p.m g.p.fl.target g.p.n M g.spills
        ⟨a.dest, a.pos, a.blkOff, a.blkExc⟩ := by
  obtain ⟨_, _, _, _, hlen, _, hnops⟩ := h.header.localHdr h.localLength
  dsimp only
  rw [emissionGhost_restore, hlen, hnops]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, List.take_zero, List.map_nil]
  exact (h.ctorP hok hp).symm

theorem EmitCountLI.runA (h : EmitCountLI P g M F s ra lo locals t)
    (hok : g.Ok) (hm : MapInv g.p.m g.p.n M)
    (hp : locals[4115]? = some (Flat.unmappedFrom (countState g M) 0 0)) :
    runA (EmissionLocals.ofList locals h.localLength).planned.pos
      (emissionGhost g hok (localEmissionHdr locals h.localLength)) t := by
  change RunU.Safe (localMapping locals h.localLength).pos
    (flat (emissionGhost g hok (localEmissionHdr locals h.localLength))) (4 * g.p.m.toNat)
  rw [h.mappingEq _, h.ghost_ctor hok hp]
  exact ctorP_safe hm _ _ _ _

theorem EmitCountLI.callLocals (h : EmitCountLI P g M F s ra lo locals t) :
    (EmissionLocals.ofList locals h.localLength).toList
      (emissionHdr g (localEmissionHdr locals h.localLength))
      (t.regs.rsp.toBitVec + 96#64) = locals := by
  rw [h.hdr_fixed]
  have he := emission_local_partition locals h.localLength
  rw [local_word_eq (by rw [h.localLength]; decide) h.original] at he
  exact he

end
end FlatShuffler.Unit.PlannerRunU
