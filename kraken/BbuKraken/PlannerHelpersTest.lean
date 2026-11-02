module

public import BbuKraken.PlannerHelpers
import all BbuKraken.PlannerHelpers
public import BbuKraken.Bin
import all BbuKraken.Bin

@[expose] public section

namespace Bbu

-- The helper specifications are closed over the assembly in the host program.
example [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.plannerDecls
    PlannerHelperSpecs :=
  planner_helpers_correct L X

example :
    letI := binLinked.plannerDecls
    PlannerHelperSpecs :=
  planner_helpers_correct binLinked binBoundary

-- Only C++ function entries are declarations. An internal block and a test wrapper
-- cannot be used as a callee in this table.
example [Host] (L : Linked) :
    L.plannerFunctions.lookup ".LB.Emission.isAvailable.0" = none := rfl

example [Host] (L : Linked) : L.plannerFunctions.lookup "plan" = none := rfl

-- Duplicate table keys keep the first declaration, as `FunDecls.at` does.
example [Host] (L : Linked) :
    (⟨[L.frag isSpilledAsm isSpilled_at, L.frag isSpilledAsm isSpilled_at]⟩ : FunDecls).at
        (label Names.isSpilled) = some (L.frag isSpilledAsm isSpilled_at) := by
  apply Linked.decl_of_lookup (fs := [
    (Names.isSpilled, L.frag isSpilledAsm isSpilled_at),
    (Names.isSpilled, L.frag isSpilledAsm isSpilled_at)])
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst x
    exact head_of_isInfixAt _ rfl (by rintro ⟨⟩)
  · rfl

end Bbu
