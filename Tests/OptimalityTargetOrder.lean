import Shuffler.Optimality.Schedule.Append.GapCost

namespace Tests.OptimalityTargetOrder

open Shuffler.Optimality Shuffler.Placement

private def a : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def short : Stack := a :: List.replicate 15 zero ++ [a]
private def long : Stack := a :: List.replicate 16 zero ++ [a]
private def repeated : Stack := a :: List.replicate 16 zero ++ a :: List.replicate 16 zero ++ [a]
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨0, by decide⟩)

private theorem allFree : ∀ value ∈ long, Free spills value := by
  intro value hv
  simp [long] at hv
  rcases hv with rfl | rfl | rfl <;> decide

-- The last first-copy DUP is DUP16. The next gap requires another LOAD.
#guard (Schedule.appendCandidate costs .gasOnly spills [] short short).map
  (fun result => (traceCost costs result.trace).score .gasOnly) = some 39
#guard (Schedule.appendCandidate costs .gasOnly spills [] long long).map
  (fun result => (traceCost costs result.trace).score .gasOnly) = some 44
#guard GapCost.bound costs .gasOnly spills [] short = 0
#guard GapCost.bound costs .gasOnly spills [] long = 3
#guard baseline costs .gasOnly spills [] long = 41

-- The condition does not restrict the number of copies or long gaps.
#guard (Schedule.appendCandidate costs .gasOnly spills [] repeated repeated).map
  (fun result => (traceCost costs result.trace).score .gasOnly) = some 82
#guard GapCost.bound costs .gasOnly spills [] repeated = 6

-- PUSH0 remains cheaper than DUP even when the copy is readable.
#guard (Schedule.appendCandidate costs .gasOnly ∅ [] [zero, zero, zero] {zero, zero, zero}).map
  (fun result => (traceCost costs result.trace).score .gasOnly) = some 6

example : ∃ result, Schedule.build costs .gasOnly spills [] long long = some result ∧
    WeightedOptimal costs .gasOnly long result.trace :=
  Schedule.build_cpp_gas_weightedOptimal _ _ spills long allFree

example (pushEncoding : Value → PushEncoding) (loadEncoding : VarId → PushEncoding) :
    ∃ result, Schedule.build (PrimitiveCosts.evm pushEncoding loadEncoding) .gasOnly
        spills [] long long = some result ∧
      WeightedOptimal (PrimitiveCosts.evm pushEncoding loadEncoding) .gasOnly long result.trace :=
  Schedule.build_evm_gas_weightedOptimal pushEncoding loadEncoding spills long allFree

example : ∃ result, Schedule.appendCandidate costs .gasOnly spills [] long long = some result ∧
    WeightedOptimal costs .gasOnly long result.trace :=
  Schedule.appendCandidate_weightedOptimal_of_premium_le_swap costs .gasOnly spills long allFree
    (fun value _ => Schedule.cpp_gas_premium_le_swap _ _ spills value)

-- Byte costs meet the factor-two boundary: premium2, SWAP1.
example : directPrice costs .bytesOnly spills a - unitPrice costs .bytesOnly spills a =
    2 * costs.swap.score .bytesOnly := by decide
#guard baseline costs .bytesOnly spills [] long = 20
#guard GapCost.bound costs .bytesOnly spills [] long = 1
#guard (Schedule.appendCandidate costs .bytesOnly spills [] long long).map
  (fun result => (traceCost costs result.trace).score .bytesOnly) = some 22

example : ∃ result, Schedule.buildWith [] costs .bytesOnly spills [] long long = some result ∧
    ∀ other : Trace spills [] long, Eligible long other →
      (traceCost costs result.trace).score .bytesOnly - baseline costs .bytesOnly spills [] long ≤
        2 * ((traceCost costs other).score .bytesOnly - baseline costs .bytesOnly spills [] long) := by
  apply Schedule.buildWith_surplus_le [] costs .bytesOnly spills long 2 (by decide) allFree
  intro value hv
  simp [long] at hv
  rcases hv with rfl | rfl | rfl <;> decide

-- Above that boundary the append candidate can exceed factor two.
private def costly : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨1, by decide⟩)
private def moved : Option (BuiltTrace spills [] long long) :=
  replayExact spills [] long long
    ([.load ⟨42⟩] ++ List.replicate 15 (.push zero) ++ [.dup 16, .push zero, .swap 1])

example : ¬(directPrice costly .bytesOnly spills a - unitPrice costly .bytesOnly spills a ≤
    2 * costly.swap.score .bytesOnly) := by decide
#guard baseline costly .bytesOnly spills [] long = 21
#guard (Schedule.appendCandidate costly .bytesOnly spills [] long long).map
  (fun result => (traceCost costly result.trace).score .bytesOnly) = some 24
#guard moved.map (fun result => (traceCost costly result.trace).score .bytesOnly) = some 22
#guard 24 - 21 > 2 * (22 - 21)

-- The direct-introduction premise cannot be omitted for an empty source.
#guard (Schedule.appendCandidate costs .gasOnly ∅ [] [a] {a}).isNone

example : ∃ result, Schedule.build costs .gasOnly spills [] [] 0 = some result ∧
    WeightedOptimal costs .gasOnly 0 result.trace :=
  Schedule.build_cpp_gas_weightedOptimal _ _ spills [] (by simp)

private def freeSwap : PrimitiveCosts := { costs with swap := Cost.zero }

example : ∃ result, Schedule.appendCandidate freeSwap .gasOnly ∅ [] [zero, zero] {zero, zero} = some result ∧
    WeightedOptimal freeSwap .gasOnly {zero, zero} result.trace := by
  apply Schedule.appendCandidate_weightedOptimal_of_premium_le_swap freeSwap .gasOnly ∅ [zero, zero]
  · intro value hv
    simp at hv
    subst value
    decide
  · intro value hv
    simp at hv
    subst value
    decide

#print axioms GapCost.targetOrder_trace_bound
#print axioms Schedule.buildWith_surplus_le
#print axioms Schedule.build_evm_gas_weightedOptimal
#print axioms Schedule.build_cpp_gas_weightedOptimal

end Tests.OptimalityTargetOrder
