module

public import PlanBridge.Interface
import all PlanBridge.Entry

/-! The Shuffler contract for the native planner input and result. -/

namespace PlanBridge

public def InputOk (i : Input) : Prop :=
  i.planner.m.toNat ≤ Bbu.MAX_N ∧ i.planner.n.toNat ≤ Bbu.MAX_N ∧
    SlotsOk (i.planner.source.toList.take i.planner.m.toNat ++
      i.planner.target.toList.take i.planner.n.toNat) ∧
    DnR (Vector.replicate (srcOf i.planner.source i.planner.m).length (0 : Byte))
      i.state.dropped

public def ResultOk (i : Input) (r : FlatResult) : Prop :=
  RunR i.planner r
    (Shuffler.Planner.run (srcOf i.planner.source i.planner.m)
      (srcOf i.planner.target i.planner.n)
      (pSpills (i.planner.source.toList.take i.planner.m.toNat) i.planner.n.toNat
        i.planner.target i.state.spills)
      i.planner.allowed (if i.takeWildcardSlots then .Take else .Leave))

public theorem flat_to_shuffler (i : Input) (us : Nat → Bbu.Flat.RunU)
    (ok : InputOk i) : ResultOk i (i.run us) :=
  plannerRun_corr ok.1 ok.2.1 ok.2.2.1 i.takeWildcardSlots i.state us ok.2.2.2

end PlanBridge
