module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderView
import all FlatShuffler.Unit.Plan.PlannerRunBuilderView
public import FlatShuffler.Unit.Defs
import all FlatShuffler.Unit.Defs
public import FlatShuffler.Unit.Plan.PlannerRunData
import all FlatShuffler.Unit.Plan.PlannerRunData

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def emissionHdr (g : PlannerCallMemory) (h : Hdr) : Hdr :=
  { h with tgt := g.p.tgt, n := g.p.n, spl := g.p.spl, data := g.dataPtr, ops := g.opsPtr }

def emissionGhost (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) : G where
  h := emissionHdr g h
  xs := g.dataCapacity - g.p.n.toNat
  xo := 4 * g.p.m.toNat
  stk := ⟨(g.data.toList.take g.dataCapacity).toArray, by
    have hm := hok.planner.m
    have hn := hok.planner.n
    simp only [List.size_toArray, List.length_take, Vector.length_toList,
      emissionHdr, PlannerCallMemory.dataCapacity]
    omega⟩
  ops := ⟨g.ops.toArray, by simpa only [List.size_toArray, emissionHdr] using hok.ops⟩
  tgt := ⟨g.p.tw.toArray, by simpa only [List.size_toArray, emissionHdr] using hok.planner.tw⟩
  spl := g.spills

theorem emissionGhost_stk (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).stk.toList = g.data.toList.take g.dataCapacity := by
  simp only [emissionGhost, Vector.toList_mk]

theorem emissionGhost_ops (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).ops.toList = g.ops := by
  simp only [emissionGhost, Vector.toList_mk]

theorem emissionGhost_tgt (g : PlannerCallMemory) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).tgt.toList = g.p.tw := by
  simp only [emissionGhost, Vector.toList_mk]

end FlatShuffler.Unit.PlannerRunU
