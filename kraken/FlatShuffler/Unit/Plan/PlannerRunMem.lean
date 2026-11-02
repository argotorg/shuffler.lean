module

public import FlatShuffler.Unit.Plan.PlannerRunDefs
import all FlatShuffler.Unit.Plan.PlannerRunDefs

@[expose] public section

/-! Memory access to the buffers and fields owned by `Planner::run`. -/

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep

def withSaw (g : PlannerCallMemory) (x : BitVec 8) : PlannerCallMemory :=
  { g with p := { g.p with saw := x } }

theorem withSaw_ok {g : PlannerCallMemory} (h : g.Ok) (x : BitVec 8) : (withSaw g x).Ok := by
  exact ⟨⟨h.planner.m, h.planner.n, h.planner.sw, h.planner.tw⟩,
    h.spillCount, h.sourceIds, h.targetIds, h.ops, h.traceLength⟩

theorem withSaw_state (g : PlannerCallMemory) (x : BitVec 8) :
    (withSaw g x).state = { g.state with saw := x != 0#8 } := rfl

section
variable {P : Addr} {g : PlannerCallMemory} {F : MProp 64} {m : Mem 64}

theorem pv (h : (plannerCallOwnedMemory P g ∗ F).get m) :
    ∃ R, (plannerObjectOwnedMemory P g.p ∗ R).get m := by
  exact ⟨_, (by unfold plannerCallOwnedMemory; ecancel :
    plannerCallOwnedMemory P g ∗ F = plannerObjectOwnedMemory P g.p ∗ _) ▸ h⟩

theorem data (h : (plannerCallOwnedMemory P g ∗ F).get m) :
    ∃ R, (Arr g.dataPtr (g.data.toList.take g.dataCapacity) ∗ R).get m := by
  exact ⟨_, (by unfold plannerCallOwnedMemory; ecancel :
    plannerCallOwnedMemory P g ∗ F = Arr g.dataPtr (g.data.toList.take g.dataCapacity) ∗ _) ▸ h⟩

theorem sources (h : (plannerCallOwnedMemory P g ∗ F).get m) :
    ∃ R, (Arr g.sourcesPtr (g.sources.toList.take g.p.n.toNat) ∗ R).get m := by
  exact ⟨_, (by unfold plannerCallOwnedMemory; ecancel :
    plannerCallOwnedMemory P g ∗ F = Arr g.sourcesPtr (g.sources.toList.take g.p.n.toNat) ∗ _) ▸ h⟩

theorem dropped (h : (plannerCallOwnedMemory P g ∗ F).get m) :
    ∃ R, (Bs g.p.drp (g.dropped.toList.take g.p.m.toNat) ∗ R).get m := by
  exact ⟨_, (by unfold plannerCallOwnedMemory; ecancel :
    plannerCallOwnedMemory P g ∗ F = Bs g.p.drp (g.dropped.toList.take g.p.m.toNat) ∗ _) ▸ h⟩

theorem store_saw (h : (plannerCallOwnedMemory P g ∗ F).get m) (x : Int) :
    (plannerCallOwnedMemory P (withSaw g (BitVec.ofInt 8 x)) ∗ F).get
      (m.storeInt (P + 56#64) 1 x) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v, plannerCallOwnedMemory P (withSaw g v) ∗ F =
      B8 (P + 56#64) v ∗ R :=
    ⟨_, fun v => by simp only [plannerCallOwnedMemory, plannerObjectOwnedMemory, withSaw, PlannerCallMemory.dataCapacity]; ecancel⟩
  rw [e]
  exact B8.store (e g.p.saw ▸ h) x

theorem isSome_saw (h : (plannerCallOwnedMemory P g ∗ F).get m) :
    (m.loadInt (P + 56#64) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, plannerCallOwnedMemory P g ∗ F = B8 (P + 56#64) g.p.saw ∗ R :=
    ⟨_, by unfold plannerCallOwnedMemory plannerObjectOwnedMemory; ecancel⟩
  exact B8.isSome (e ▸ h)

theorem store_data (h : (plannerCallOwnedMemory P g ∗ F).get m) {i : Word}
    (hi : i.toNat < MAX_N) (hcap : i.toNat < g.dataCapacity) (w : Word) :
    (plannerCallOwnedMemory P { g with data := Flat.put g.data i w } ∗ F).get
      (m.storeInt (slotAt g.dataPtr i.toNat) 8 w.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v : Vector Word MAX_N,
      plannerCallOwnedMemory P { g with data := v } ∗ F = Arr g.dataPtr (v.toList.take g.dataCapacity) ∗ R :=
    ⟨_, fun v => by simp only [PlannerCallMemory.dataCapacity, plannerCallOwnedMemory]; ecancel⟩
  rw [e]
  simpa [Flat.put, slotAt, PlannerCallMemory.dataCapacity, List.take_set] using
    Arr.store (e g.data ▸ h) (by
      simp only [List.length_take, Vector.length_toList]
      change i.toNat < min g.dataCapacity MAX_N
      omega) w

theorem store_sources (h : (plannerCallOwnedMemory P g ∗ F).get m) {i : Word}
    (hi : i.toNat < MAX_N) (hn : i.toNat < g.p.n.toNat) (w : Word) :
    (plannerCallOwnedMemory P { g with sources := Flat.put g.sources i w } ∗ F).get
      (m.storeInt (slotAt g.sourcesPtr i.toNat) 8 w.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v : Vector Word MAX_N,
      plannerCallOwnedMemory P { g with sources := v } ∗ F = Arr g.sourcesPtr (v.toList.take g.p.n.toNat) ∗ R :=
    ⟨_, fun v => by simp only [PlannerCallMemory.dataCapacity, plannerCallOwnedMemory]; ecancel⟩
  rw [e]
  simpa [Flat.put, slotAt, List.take_set] using
    Arr.store (e g.sources ▸ h) (by
      simp only [List.length_take, Vector.length_toList]
      omega) w

theorem store_count (h : (plannerCallOwnedMemory P g ∗ F).get m) (w : Word) :
    (plannerCallOwnedMemory P { g with count := w } ∗ F).get
      (m.storeInt g.countPtr 8 w.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v : Word,
      plannerCallOwnedMemory P { g with count := v } ∗ F = Wd g.countPtr v ∗ R :=
    ⟨_, fun v => by simp only [PlannerCallMemory.dataCapacity, plannerCallOwnedMemory]; ecancel⟩
  rw [e]
  exact Wd.store (e g.count ▸ h) w

end
end FlatShuffler.Unit.PlannerRunU
