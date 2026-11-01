module

public import BbuKraken.Unit.Plan.PlannerRunEmissionReady
import all BbuKraken.Unit.Plan.PlannerRunEmissionReady
public import BbuKraken.Unit.Plan.PlannerRunOutputDefs
import all BbuKraken.Unit.Plan.PlannerRunOutputDefs

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem EmissionLocals.head_get (l : EmissionLocals) (h : Hdr) (PM : Addr)
    (i : Nat) (hi : i < 12) :
    (l.toList h PM)[i]? = l.head.toList[i]? := by
  simp only [EmissionLocals.toList, List.append_assoc]
  rw [List.getElem?_append_left (by simpa only [Vector.length_toList] using hi)]

theorem EmissionLocals.destSlice (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    ((l.toList h PM).drop 12).take 1024 = l.planned.dest.toList := by
  have hd : l.planned.dest.toList.length = 1024 := Vector.length_toList
  simp [EmissionLocals.toList, hd]

theorem EmissionLocals.posSlice (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    ((l.toList h PM).drop 1036).take 1024 = l.planned.pos.toList := by
  have hd : l.planned.dest.toList.length = 1024 := Vector.length_toList
  have hp : l.planned.pos.toList.length = 1024 := Vector.length_toList
  simp [EmissionLocals.toList, List.drop_append, List.take_append, hd, hp]

theorem EmissionLocals.mapping (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    localMapping (l.toList h PM) (l.length h PM) = l.planned := by
  cases hm : l.planned with
  | mk dest pos =>
    have hd := l.destSlice h PM
    have hp := l.posSlice h PM
    simp only [hm] at hd hp
    simp only [localMapping, hd, hp, Vector.toArray_toList]

theorem EmissionLocals.nops (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    (l.toList h PM)[2066]? = some h.nops := by
  have hd : l.planned.dest.toList.length = 1024 := Vector.length_toList
  have hp : l.planned.pos.toList.length = 1024 := Vector.length_toList
  simp [EmissionLocals.toList, List.append_assoc, List.getElem?_append,
    hd, hp, emissionWords]

section
variable {P : Addr} {g : PlannerRunG} {M : Flat.Mapping} {F : MProp 64}
    {s t u : MachineData} {ra : Int64} {lo lo' locals : List Word}

theorem EmitCountLI.postEmission (h : EmitCountLI P g M F s ra lo locals t)
    (hok : g.Ok) (a : G)
    (hk : Keep (emissionGhost g hok (localEmissionHdr locals h.localLength)) a)
    (hb : Bd P (emissionResult g hok (localEmissionHdr locals h.localLength) a hk)
      F s ra lo' ((EmissionLocals.ofList locals h.localLength).toList a.h
        (t.regs.rsp.toBitVec + 96#64)) u)
    (ha : a.Ok) (hag : Sep.mod.Agree t u) :
    PostEmitLI P (emissionResult g hok (localEmissionHdr locals h.localLength) a hk)
      M F s ra lo' ((EmissionLocals.ofList locals h.localLength).toList a.h
        (t.regs.rsp.toBitVec + 96#64)) u := by
  let l := EmissionLocals.ofList locals h.localLength
  have hget (i : Nat) (hi : i < 12) :
      (l.toList a.h (t.regs.rsp.toBitVec + 96#64))[i]? = locals[i]? := by
    rw [l.head_get a.h _ i hi]
    change ((locals.take 12).toArray.toList)[i]? = locals[i]?
    simp only [List.getElem?_take, hi, ↓reduceIte]
  refine ⟨⟨hb, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, emissionResult_ok hok _ hk ha, ?_⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]
    exact h.rbx
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]
    exact h.r12
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]
    exact h.r15
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]
    exact h.r14
  · exact (hget 2 (by decide)).trans h.sources
  · exact (hget 3 (by decide)).trans h.count
  · rw [l.nops]
    simp only [emissionResult, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro hl
    exact (l.mapping a.h _).trans (h.mappingEq h.localLength)
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13,
      mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]
    exact h.r13

end
end Bbu.Unit.PlannerRunU
