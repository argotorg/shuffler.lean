module

public import BbuKraken.Unit.Plan.PlannerRunBuilderView
import all BbuKraken.Unit.Plan.PlannerRunBuilderView
public import BbuKraken.Unit.Defs
import all BbuKraken.Unit.Defs
public import BbuKraken.Unit.Plan.PlannerRunData
import all BbuKraken.Unit.Plan.PlannerRunData

@[expose] public section

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def emissionHdr (g : PlannerRunG) (h : Hdr) : Hdr :=
  { h with tgt := g.p.tgt, n := g.p.n, spl := g.p.spl, data := g.dataPtr, ops := g.opsPtr }

def emissionGhost (g : PlannerRunG) (hok : g.Ok) (h : Hdr) : G where
  h := emissionHdr g h
  xs := g.dataCapacity - g.p.n.toNat
  xo := 4 * g.p.m.toNat
  stk := ⟨(g.data.toList.take g.dataCapacity).toArray, by
    have hm := hok.planner.m
    have hn := hok.planner.n
    simp only [List.size_toArray, List.length_take, Vector.length_toList,
      emissionHdr, PlannerRunG.dataCapacity]
    omega⟩
  ops := ⟨g.ops.toArray, by simpa only [List.size_toArray, emissionHdr] using hok.ops⟩
  tgt := ⟨g.p.tw.toArray, by simpa only [List.size_toArray, emissionHdr] using hok.planner.tw⟩
  spl := g.spills

theorem emissionGhost_stk (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).stk.toList = g.data.toList.take g.dataCapacity := by
  simp only [emissionGhost, Vector.toList_mk]

theorem emissionGhost_ops (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).ops.toList = g.ops := by
  simp only [emissionGhost, Vector.toList_mk]

theorem emissionGhost_tgt (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).tgt.toList = g.p.tw := by
  simp only [emissionGhost, Vector.toList_mk]

end Bbu.Unit.PlannerRunU
