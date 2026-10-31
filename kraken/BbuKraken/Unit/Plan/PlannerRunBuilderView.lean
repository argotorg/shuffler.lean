import BbuKraken.Unit.Plan.PlannerRunBuilderLayout
import BbuKraken.Unit.Plan.PlannerRunBuilderModel

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep Flat

def builderGhost (g : PlannerRunG) (mp : Addr) (strat saw : BitVec 8)
    (M : Flat.Mapping) : BG where
  src := g.p.src
  m := g.p.m
  tgt := g.p.tgt
  n := g.p.n
  drp := g.p.drp
  strat := strat
  mp := mp
  saw := saw
  sw := g.p.sw
  tw := g.p.tw
  db := g.dropped.toList.take g.p.m.toNat
  M := M

theorem builderGhost_ok (g : PlannerRunG) (hok : g.Ok) (mp : Addr)
    (strat saw : BitVec 8) (M : Flat.Mapping) : (builderGhost g mp strat saw M).Ok := by
  refine ⟨hok.planner.m, hok.planner.n, hok.planner.sw, hok.planner.tw, ?_⟩
  simp only [builderGhost, List.length_take, Vector.length_toList]
  exact Nat.min_eq_left hok.planner.m

theorem builder_view_frame (P B : Addr) (g : PlannerRunG) (hok : g.Ok)
    (mp : Addr) (strat : BitVec 8) :
    ∃ PF, ∀ (M : Flat.Mapping) (saw : BitVec 8),
      PlannerRunView P g ∗ MapM mp M ∗ BuilderMembers B (builderGhost g mp strat saw M) =
        BView B (builderGhost g mp strat saw M) ∗ PF := by
  let headers := Wd P g.p.src ∗ Wd (P + 8#64) g.p.m ∗
    Wd (P + 16#64) g.p.tgt ∗ Wd (P + 24#64) g.p.n ∗ Wd (P + 32#64) g.p.spl ∗
    B8 (P + 40#64) g.p.allowed ∗ Wd (P + 48#64) g.p.drp ∗ B8 (P + 56#64) g.p.saw
  refine ⟨headers ∗ Spl g.p.spl g.spills (List.range g.spillCount) ∗
    Bs (g.p.drp + g.p.m) (g.dropped.toList.drop g.p.m.toNat) ∗
    Arr g.dataPtr g.data.toList ∗ Ops g.opsPtr 0 g.ops ∗
    Arr g.sourcesPtr g.sources.toList ∗ Wd g.countPtr g.count, ?_⟩
  intro M saw
  have hdrop : Bs g.p.drp g.dropped.toList =
      Bs g.p.drp (g.dropped.toList.take g.p.m.toNat) ∗
        Bs (g.p.drp + g.p.m) (g.dropped.toList.drop g.p.m.toNat) := by
    conv => lhs; rw [← List.take_append_drop g.p.m.toNat g.dropped.toList]
    rw [ResolveU.Bs_append]
    simp only [List.length_take, Vector.length_toList, Nat.min_eq_left hok.planner.m,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [PlannerRunView, PView, BView, BuilderMembers, builderGhost, headers, hdrop]
  simp only [MProp.sep_assoc]
  ac_rfl

set_option maxRecDepth 4096 in
theorem builderGhost_buildMapping (g : PlannerRunG) (hok : g.Ok) (mp : Addr)
    (strat saw : BitVec 8) (M : Flat.Mapping) :
    Flat.buildMapping (builderGhost g mp strat saw M).fl M =
      Flat.buildMapping ⟨g.p.fl.source, g.p.m, g.p.fl.target, g.p.n,
        g.dropped, strat == 1#8⟩ M := by
  have hd : ∀ p, p < g.p.m →
      get (vec (g.dropped.toList.take g.p.m.toNat)) p = get g.dropped p := by
    intro p hp
    have hl : (g.dropped.toList.take g.p.m.toNat).length = g.p.m.toNat := by
      simp only [List.length_take, Vector.length_toList, Nat.min_eq_left hok.planner.m]
    have hpN : p.toNat < g.dropped.toList.length := by
      simp only [Vector.length_toList]
      exact Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hok.planner.m
    rw [get_vecL (by rw [hl]; exact BitVec.lt_def.mp hp)
      (by rw [hl]; exact hok.planner.m), List.getElem_take, Vector.getElem_toList,
      get_toNat _ (by simpa using hpN)]
  exact buildMapping_dropped
    ⟨g.p.fl.source, g.p.m, g.p.fl.target, g.p.n, g.dropped, strat == 1#8⟩
    (vec (g.dropped.toList.take g.p.m.toNat)) hd M

end Bbu.Unit.PlannerRunU
