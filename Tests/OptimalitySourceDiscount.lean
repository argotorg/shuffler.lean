import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount.Cheapest
import Shuffler.Optimality.BirthPlacement.Dual.SourceDiscount.Trace

namespace Tests.OptimalitySourceDiscount

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement Dual

private def a : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)

private def emptySource : SourcePlan spills [] [a, a] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

example : (emptySource.cheapest costs .bytesOnly).method 0 = .direct := by decide
example : (emptySource.cheapest costs .bytesOnly).method 1 = .dup := by decide

private def repeated : SourcePlan spills [a, a] [a, a, a, a] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

-- The first two copies already exist. Their internal gap has no reward.
example : (sourceTargetGap costs .bytesOnly spills [a, a] [a, a, a, a] 0).reward = 0 := by decide
example : (sourceTargetGap costs .bytesOnly spills [a, a] [a, a, a, a] 1).reward = 66 := by decide
example : (sourceTargetGap costs .bytesOnly spills [a, a] [a, a, a, a] 2).reward = 66 := by decide
example : (sourceTargetGap costs .bytesOnly spills [a, a] [a, a, a, a] 3).reward = 0 := by decide
example : sourceDirectTotal costs .bytesOnly spills [a, a] [a, a, a, a] = 68 := by decide
example : eventScore costs .bytesOnly spills (repeated.cheapest costs .bytesOnly).events = 2 := by decide
example : 2 * sourceDirectTotal costs .bytesOnly spills [a, a] [a, a, a, a] =
    2 * eventScore costs .bytesOnly spills (repeated.cheapest costs .bytesOnly).events +
      ∑ index, (sourceTargetGap costs .bytesOnly spills [a, a] [a, a, a, a] index).reward *
        sourcePlanReuse costs .bytesOnly (repeated.cheapest costs .bytesOnly) index :=
  source_cheapest_generation_discount_eq costs .bytesOnly repeated

-- A hard value uses DUP's price for accounting and has no optional reward.
private def hard : SourcePlan ∅ [a, a] [a, a, a] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .dup
  available := by decide

example : ¬ Shuffler.Placement.Free ∅ a := by decide
example : sourceDirectTotal costs .bytesOnly ∅ [a, a] [a, a, a] = 1 := by decide
example : ∀ index : Fin 3, (sourceTargetGap costs .bytesOnly ∅ [a, a] [a, a, a] index).reward = 0 := by decide
example : 2 * sourceDirectTotal costs .bytesOnly ∅ [a, a] [a, a, a] =
    2 * eventScore costs .bytesOnly ∅ (hard.cheapest costs .bytesOnly).events +
      ∑ index, (sourceTargetGap costs .bytesOnly ∅ [a, a] [a, a, a] index).reward *
        sourcePlanReuse costs .bytesOnly (hard.cheapest costs .bytesOnly) index :=
  source_cheapest_generation_discount_eq costs .bytesOnly hard

-- The real birth is at absolute row 17 in both plans.
private def deepSource : Stack := a :: List.replicate 16 zero
private def nearSource : Stack := zero :: a :: List.replicate 15 zero

private def deep : SourcePlan spills deepSource (deepSource ++ [a]) where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

private def near : SourcePlan spills nearSource (nearSource ++ [a]) where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

example : (deep.cheapest costs .bytesOnly).method ⟨0, by decide⟩ = .direct := by decide
example : (near.cheapest costs .bytesOnly).method ⟨0, by decide⟩ = .dup := by decide
example : sourcePlanReuse costs .bytesOnly deep ⟨0, by decide⟩ = 0 := by decide
example : sourcePlanReuse costs .bytesOnly near ⟨1, by decide⟩ = 1 := by decide

-- A positive optional price now certifies a production source trace.
private def witness :=
  (replayExact spills [a, a] [a, a, a] ([a] : Multiset Value) [.dup 1]).get (by decide)

private def certificate : Certificate 3 3 where
  scale := 1
  row := fun _ => 0
  column := fun _ => 67
  quotaWeight index := if index = 1 then 66 else 0
  capWeight := fun _ => 0

example : certificate.lowerNumerator (sourceTargetGap costs .bytesOnly spills [a, a] [a, a, a])
    (sourceDirectTotal costs .bytesOnly spills [a, a] [a, a, a]) (costs.swap.score .bytesOnly) = 2 := by decide

example (other : Trace spills [a, a] [a, a, a]) (hpop : other.noPop) :
    (traceCost costs witness.trace).score .bytesOnly - sourceBaseline costs .bytesOnly spills [a, a] [a, a, a] ≤
      2 * ((traceCost costs other).score .bytesOnly - sourceBaseline costs .bytesOnly spills [a, a] [a, a, a]) :=
  Certificate.source_optional_surplus_le_twice (source := [a, a]) (target := [a, a, a])
    certificate costs .bytesOnly (by decide) witness.trace (by decide) other hpop

-- A price attached to an old-only gap cannot claim the new-copy reward.
example : ¬ Certificate.ValidOn (target := [a, a, a]) certificate (targetGap costs .bytesOnly spills [a, a, a])
    (costs.swap.score .bytesOnly) (sourceAllowed [a, a] [a, a, a]) := by decide

private def noGrowth : SourcePlan spills [a, a] [a, a] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := Fin.elim0
  available := by decide

example : sourceDirectTotal costs .bytesOnly spills [a, a] [a, a] = 0 := by decide
example : ∀ index : Fin 2, sourcePlanReuse costs .bytesOnly noGrowth index *
    (sourceTargetGap costs .bytesOnly spills [a, a] [a, a] index).reward = 0 := by decide

#print axioms source_generation_discount
#print axioms source_cheapest_generation_discount_eq
#print axioms Certificate.source_optional_trace_lower_le
#print axioms Certificate.source_optional_surplus_le_twice

end Tests.OptimalitySourceDiscount
