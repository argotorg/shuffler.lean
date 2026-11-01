module

public import PlanBridge.Interface
import all PlanBridge.Entry

/-! The Shuffler contract. Its implementation imports stay private. -/

namespace PlanBridge

public def InputOk (i : Input) : Prop :=
  SlotsOk (i.source.toList.take i.m.toNat ++ i.target.toList.take i.n.toNat)

public def ResultOk (i : Input) (r : FlatResult) : Prop :=
  match r.2 with
  | none => r.1 = -2
  | some s => r.1 = codeOf s ∧
      RunR ⟨i.source, i.m, i.target, i.n, i.allowed = 1⟩ s
        (Shuffler.Planner.run (srcOf i.source i.m) (srcOf i.target i.n)
          (pSpills (i.source.toList.take i.m.toNat) i.n.toNat i.target i.spilled)
          (i.allowed = 1) (if decide (i.strategy = 1) then .Take else .Leave))

public theorem flat_to_shuffler (i : Input) (us : Nat → Bbu.Flat.RunU)
    (ok : InputOk i) : ResultOk i (i.run us) := by
  have h := planEntry_corr i.m i.n i.source i.target i.spilled i.idCount i.allowed
    i.strategy i.dropped i.data i.sources us ok
  unfold ResultOk Input.run
  generalize Bbu.Flat.planEntry i.m i.n i.source i.target i.spilled i.idCount
    i.allowed i.strategy i.dropped i.data i.sources us = r at h ⊢
  rcases r with ⟨c, _ | s⟩
  · exact h
  · exact h.2.2

end PlanBridge
