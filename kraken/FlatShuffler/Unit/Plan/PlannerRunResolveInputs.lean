module

public import FlatShuffler.Unit.Plan.PlannerRunResolveDefs
import all FlatShuffler.Unit.Plan.PlannerRunResolveDefs
public import FlatShuffler.Unit.Plan.PlannerRunEmissionPost
import all FlatShuffler.Unit.Plan.PlannerRunEmissionPost
public import FlatShuffler.Unit.Plan.PlannerRunBlockedBasic
import all FlatShuffler.Unit.Plan.PlannerRunBlockedBasic

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

structure EmissionCells (locals : List Word) (hl : locals.length = 4121)
    (out : Flat.St) : Prop where
  size : resolveSize locals hl = out.size
  offset : resolveOffset locals hl = out.blockedOffset
  excess : resolveExcess locals hl = out.blockedExcess
  current : localCurrentMapping locals hl = ⟨out.dest, out.pos⟩

theorem EmissionLocals.resolveSize (l : EmissionLocals) (h : Hdr) (PM : Addr)
    (hl : (l.toList h PM).length = 4121) : resolveSize (l.toList h PM) hl = h.len := by
  apply local_word_eq (i := 2064) (by omega)
  simp only [EmissionLocals.toList, List.append_assoc, List.getElem?_append,
    emissionWords, Vector.length_toList]
  simp [MAX_N]

theorem EmissionLocals.resolveOffset (l : EmissionLocals) (h : Hdr) (PM : Addr)
    (hl : (l.toList h PM).length = 4121) : resolveOffset (l.toList h PM) hl = h.blkOff := by
  apply local_word_eq (i := 4116) (by omega)
  simp only [EmissionLocals.toList, List.append_assoc, List.getElem?_append,
    emissionWords, Vector.length_toList]
  simp [MAX_N]

theorem EmissionLocals.resolveExcess (l : EmissionLocals) (h : Hdr) (PM : Addr)
    (hl : (l.toList h PM).length = 4121) : resolveExcess (l.toList h PM) hl = h.blkExc := by
  apply local_word_eq (i := 4117) (by omega)
  simp only [EmissionLocals.toList, List.append_assoc, List.getElem?_append,
    emissionWords, Vector.length_toList]
  simp [MAX_N]

theorem EmissionLocals.currentDestSlice (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    ((l.toList h PM).drop 2067).take 1024 = h.dest.toList := by
  have hd : l.planned.dest.toList.length = 1024 := Vector.length_toList
  have hp : l.planned.pos.toList.length = 1024 := Vector.length_toList
  have hc : h.dest.toList.length = 1024 := Vector.length_toList
  simp [EmissionLocals.toList, List.drop_append, hd, hp, hc, emissionWords,
    List.drop_eq_nil_of_le]

theorem EmissionLocals.currentPosSlice (l : EmissionLocals) (h : Hdr) (PM : Addr) :
    ((l.toList h PM).drop 3091).take 1024 = h.pos.toList := by
  have hd : l.planned.dest.toList.length = 1024 := Vector.length_toList
  have hp : l.planned.pos.toList.length = 1024 := Vector.length_toList
  have hc : h.dest.toList.length = 1024 := Vector.length_toList
  have hc' : h.pos.toList.length = 1024 := Vector.length_toList
  simp [EmissionLocals.toList, List.drop_append, hd, hp, hc, hc', emissionWords,
    List.drop_eq_nil_of_le]

theorem EmissionLocals.currentMapping (l : EmissionLocals) (h : Hdr) (PM : Addr)
    (hl : (l.toList h PM).length = 4121) :
    localCurrentMapping (l.toList h PM) hl = ⟨h.dest, h.pos⟩ := by
  simp only [localCurrentMapping, l.currentDestSlice h PM, l.currentPosSlice h PM,
    Vector.toArray_toList]

theorem EmissionLocals.cells (l : EmissionLocals) (a : G) (PM : Addr)
    (hl : (l.toList a.h PM).length = 4121) :
    EmissionCells (l.toList a.h PM) hl (flat a) :=
  ⟨l.resolveSize a.h PM hl, l.resolveOffset a.h PM hl, l.resolveExcess a.h PM hl,
    l.currentMapping a.h PM hl⟩

theorem EmissionCells.resolveInputs {g : PlannerCallMemory} {M : Flat.Mapping}
    {locals : List Word} {hl : locals.length = 4121} {out : Flat.St}
    (h : EmissionCells locals hl out) (hb : BlockedBounds g.p.n out)
    (hm : MapInv g.p.m g.p.n M) : ResolveInputs g M locals hl := by
  refine ⟨hm, h.size ▸ hb.size, h.offset ▸ hb.offset, h.excess ▸ hb.excess, ?_⟩
  rw [h.current, h.size]
  exact hb.current

theorem EmissionCells.resolved {g : PlannerCallMemory} {M : Flat.Mapping}
    {locals : List Word} {hl : locals.length = 4121} {out : Flat.St}
    {spills : BitVec 32 → BitVec 8} {dropped : Vector (BitVec 8) MAX_N}
    {res : Flat.Resolution} (h : EmissionCells locals hl out)
    (hr : Resolved g M locals hl spills dropped res) :
    ∀ scratch : Flat.ResolveU, Flat.resolve g.p.fl g.spills g.dropped M
      out.blockedOffset out.blockedExcess ⟨out.dest, out.pos⟩ out.size scratch =
        (res, spills, dropped) := by
  simpa only [Resolved, h.offset, h.excess, h.current, h.size] using hr

end FlatShuffler.Unit.PlannerRunU
