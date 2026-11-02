module

public import BbuKraken.FlatPlan

/-! The inputs and result of `Planner::run`, shared by the two contracts. -/

@[expose] public section

namespace PlanBridge

structure Input where
  planner : Bbu.Flat.Planner
  takeWildcardSlots : Bool
  state : Bbu.Flat.PSt

abbrev FlatResult := Bbu.Flat.Status × Bbu.Flat.PSt

def Input.run (i : Input) (us : Nat → Bbu.Flat.RunU) : FlatResult :=
  Bbu.Flat.plannerRun i.planner i.takeWildcardSlots i.state us

end PlanBridge
