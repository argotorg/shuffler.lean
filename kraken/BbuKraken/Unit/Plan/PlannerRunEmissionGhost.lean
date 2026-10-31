import BbuKraken.Unit.Plan.PlannerRunBuilderView
import BbuKraken.Unit.Defs

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def emissionHdr (g : PlannerRunG) (h : Hdr) : Hdr :=
  { h with tgt := g.p.tgt, n := g.p.n, spl := g.p.spl, data := g.dataPtr, ops := g.opsPtr }

def emissionGhost (g : PlannerRunG) (hok : g.Ok) (h : Hdr) : G where
  h := emissionHdr g h
  xs := MAX_N - g.p.n.toNat
  xo := 4 * g.p.m.toNat
  stk := g.data.cast (by
    change MAX_N = g.p.n.toNat + (MAX_N - g.p.n.toNat)
    have := hok.planner.n
    omega)
  ops := ⟨g.ops.toArray, by simpa only [List.size_toArray, emissionHdr] using hok.ops⟩
  tgt := ⟨g.p.tw.toArray, by simpa only [List.size_toArray, emissionHdr] using hok.planner.tw⟩
  spl := g.spills

theorem emissionGhost_stk (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).stk.toList = g.data.toList := rfl

theorem emissionGhost_ops (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).ops.toList = g.ops := by
  simp only [emissionGhost, Vector.toList_mk, List.toList_toArray]

theorem emissionGhost_tgt (g : PlannerRunG) (hok : g.Ok) (h : Hdr) :
    (emissionGhost g hok h).tgt.toList = g.p.tw := by
  simp only [emissionGhost, Vector.toList_mk, List.toList_toArray]

end Bbu.Unit.PlannerRunU
