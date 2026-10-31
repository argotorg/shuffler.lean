import BbuKraken.Unit.Plan.PlannerRunDefs

/-! Memory access to the buffers and fields owned by `Planner::run`. -/

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

def withSaw (g : PlannerRunG) (x : BitVec 8) : PlannerRunG :=
  { g with p := { g.p with saw := x } }

theorem withSaw_ok {g : PlannerRunG} (h : g.Ok) (x : BitVec 8) : (withSaw g x).Ok := by
  exact ⟨⟨h.planner.m, h.planner.n, h.planner.sw, h.planner.tw⟩,
    h.spillCount, h.sourceIds, h.targetIds, h.ops, h.traceLength⟩

theorem withSaw_state (g : PlannerRunG) (x : BitVec 8) :
    (withSaw g x).state = { g.state with saw := x != 0#8 } := rfl

section
variable {P : Addr} {g : PlannerRunG} {F : MProp 64} {m : Mem 64}

theorem pv (h : (PlannerRunView P g ∗ F).get m) :
    ∃ R, (PView P g.p ∗ R).get m := by
  exact ⟨_, (by unfold PlannerRunView; ecancel :
    PlannerRunView P g ∗ F = PView P g.p ∗ _) ▸ h⟩

theorem data (h : (PlannerRunView P g ∗ F).get m) :
    ∃ R, (Arr g.dataPtr g.data.toList ∗ R).get m := by
  exact ⟨_, (by unfold PlannerRunView; ecancel :
    PlannerRunView P g ∗ F = Arr g.dataPtr g.data.toList ∗ _) ▸ h⟩

theorem sources (h : (PlannerRunView P g ∗ F).get m) :
    ∃ R, (Arr g.sourcesPtr g.sources.toList ∗ R).get m := by
  exact ⟨_, (by unfold PlannerRunView; ecancel :
    PlannerRunView P g ∗ F = Arr g.sourcesPtr g.sources.toList ∗ _) ▸ h⟩

theorem dropped (h : (PlannerRunView P g ∗ F).get m) :
    ∃ R, (Bs g.p.drp g.dropped.toList ∗ R).get m := by
  exact ⟨_, (by unfold PlannerRunView; ecancel :
    PlannerRunView P g ∗ F = Bs g.p.drp g.dropped.toList ∗ _) ▸ h⟩

theorem store_saw (h : (PlannerRunView P g ∗ F).get m) (x : Int) :
    (PlannerRunView P (withSaw g (BitVec.ofInt 8 x)) ∗ F).get
      (m.storeInt (P + 56#64) 1 x) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v, PlannerRunView P (withSaw g v) ∗ F =
      B8 (P + 56#64) v ∗ R :=
    ⟨_, fun v => by simp only [PlannerRunView, PView, withSaw]; ecancel⟩
  rw [e]
  exact B8.store (e g.p.saw ▸ h) x

theorem isSome_saw (h : (PlannerRunView P g ∗ F).get m) :
    (m.loadInt (P + 56#64) 1).isSome = true := by
  obtain ⟨R, e⟩ : ∃ R, PlannerRunView P g ∗ F = B8 (P + 56#64) g.p.saw ∗ R :=
    ⟨_, by unfold PlannerRunView PView; ecancel⟩
  exact B8.isSome (e ▸ h)

theorem store_data (h : (PlannerRunView P g ∗ F).get m) {i : Word}
    (hi : i.toNat < MAX_N) (w : Word) :
    (PlannerRunView P { g with data := Flat.put g.data i w } ∗ F).get
      (m.storeInt (slotAt g.dataPtr i.toNat) 8 w.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v : Vector Word MAX_N,
      PlannerRunView P { g with data := v } ∗ F = Arr g.dataPtr v.toList ∗ R :=
    ⟨_, fun v => by simp only [PlannerRunView]; ecancel⟩
  rw [e]
  simpa [Flat.put, slotAt] using Arr.store (e g.data ▸ h) (by simpa using hi) w

theorem store_sources (h : (PlannerRunView P g ∗ F).get m) {i : Word}
    (hi : i.toNat < MAX_N) (w : Word) :
    (PlannerRunView P { g with sources := Flat.put g.sources i w } ∗ F).get
      (m.storeInt (slotAt g.sourcesPtr i.toNat) 8 w.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v : Vector Word MAX_N,
      PlannerRunView P { g with sources := v } ∗ F = Arr g.sourcesPtr v.toList ∗ R :=
    ⟨_, fun v => by simp only [PlannerRunView]; ecancel⟩
  rw [e]
  simpa [Flat.put, slotAt] using Arr.store (e g.sources ▸ h) (by simpa using hi) w

theorem store_count (h : (PlannerRunView P g ∗ F).get m) (w : Word) :
    (PlannerRunView P { g with count := w } ∗ F).get
      (m.storeInt g.countPtr 8 w.toInt) := by
  obtain ⟨R, e⟩ : ∃ R, ∀ v : Word,
      PlannerRunView P { g with count := v } ∗ F = Wd g.countPtr v ∗ R :=
    ⟨_, fun v => by simp only [PlannerRunView]; ecancel⟩
  rw [e]
  exact Wd.store (e g.count ▸ h) w

end
end Bbu.Unit.PlannerRunU
