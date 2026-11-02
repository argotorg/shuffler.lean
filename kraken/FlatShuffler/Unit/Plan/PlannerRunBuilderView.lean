module

public import FlatShuffler.Unit.Plan.PlannerRunBuilderLayout
import all FlatShuffler.Unit.Plan.PlannerRunBuilderLayout
public import FlatShuffler.Unit.Plan.PlannerRunBuilderModel
import all FlatShuffler.Unit.Plan.PlannerRunBuilderModel

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

def builderGhost (g : PlannerCallMemory) (mp : Addr) (strat saw : BitVec 8)
    (M : Flat.Mapping) : BG where
  src := g.p.src
  sourceSize := g.p.sourceSize
  tgt := g.p.tgt
  targetSize := g.p.targetSize
  drp := g.p.drp
  strat := strat
  mp := mp
  saw := saw
  sw := g.p.sw
  tw := g.p.tw
  db := g.dropped.toList.take g.p.sourceSize.toNat
  M := M

theorem builderGhost_ok (g : PlannerCallMemory) (hok : g.Ok) (mp : Addr)
    (strat saw : BitVec 8) (M : Flat.Mapping) : (builderGhost g mp strat saw M).Ok := by
  refine ⟨hok.planner.sourceSizeFitsBuffer, hok.planner.targetSizeFitsBuffer, hok.planner.sw, hok.planner.tw, ?_⟩
  simp only [builderGhost, List.length_take, Vector.length_toList]
  exact Nat.min_eq_left hok.planner.sourceSizeFitsBuffer

theorem builder_view_frame (P B : Addr) (g : PlannerCallMemory) (_hok : g.Ok)
    (mp : Addr) (strat : BitVec 8) :
    ∃ PF, ∀ (M : Flat.Mapping) (saw : BitVec 8),
      plannerCallOwnedMemory P g ∗ MapM mp M ∗ BuilderMembers B (builderGhost g mp strat saw M) =
        BView B (builderGhost g mp strat saw M) ∗ PF := by
  let headers := Wd P g.p.src ∗ Wd (P + 8#64) g.p.sourceSize ∗
    Wd (P + 16#64) g.p.tgt ∗ Wd (P + 24#64) g.p.targetSize ∗ Wd (P + 32#64) g.p.spl ∗
    B8 (P + 40#64) g.p.allowed ∗ Wd (P + 48#64) g.p.drp ∗ B8 (P + 56#64) g.p.saw
  refine ⟨headers ∗ Spl g.p.spl g.spills (List.range g.spillCount) ∗
    Arr g.dataPtr (g.data.toList.take g.dataCapacity) ∗ Ops g.opsPtr 0 g.ops ∗
    Arr g.sourcesPtr (g.sources.toList.take g.p.targetSize.toNat) ∗ Wd g.countPtr g.count, ?_⟩
  intro M saw
  simp only [PlannerCallMemory.dataCapacity, plannerCallOwnedMemory, plannerObjectOwnedMemory, BView, BuilderMembers, builderGhost, headers]
  simp only [MProp.sep_assoc]
  ac_rfl

set_option maxRecDepth 4096 in
theorem builderGhost_buildMapping (g : PlannerCallMemory) (hok : g.Ok) (mp : Addr)
    (strat saw : BitVec 8) (M : Flat.Mapping) :
    Flat.buildMapping (builderGhost g mp strat saw M).fl M =
      Flat.buildMapping ⟨g.p.fl.source, g.p.sourceSize, g.p.fl.target, g.p.targetSize,
        g.dropped, strat == 1#8⟩ M := by
  have hd : ∀ p, p < g.p.sourceSize →
      get (vec (g.dropped.toList.take g.p.sourceSize.toNat)) p = get g.dropped p := by
    intro p hp
    have hl : (g.dropped.toList.take g.p.sourceSize.toNat).length = g.p.sourceSize.toNat := by
      simp only [List.length_take, Vector.length_toList, Nat.min_eq_left hok.planner.sourceSizeFitsBuffer]
    have hpN : p.toNat < g.dropped.toList.length := by
      simp only [Vector.length_toList]
      exact Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hok.planner.sourceSizeFitsBuffer
    rw [get_vecL (by rw [hl]; exact BitVec.lt_def.mp hp)
      (by rw [hl]; exact hok.planner.sourceSizeFitsBuffer), List.getElem_take, Vector.getElem_toList,
      get_toNat _ (by simpa using hpN)]
  exact buildMapping_dropped
    ⟨g.p.fl.source, g.p.sourceSize, g.p.fl.target, g.p.targetSize, g.dropped, strat == 1#8⟩
    (vec (g.dropped.toList.take g.p.sourceSize.toNat)) hd M

end FlatShuffler.Unit.PlannerRunU
