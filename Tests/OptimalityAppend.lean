import Shuffler.Optimality.Schedule.Append.Theorems

open Shuffler.Optimality

namespace OptimalityAppendTests

private def zero : Value := .Lit 0
private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun value => if value = zero then .push0 else .push ⟨0,by decide⟩)
  (fun _ => .push ⟨0,by decide⟩)

#guard (Schedule.appendCandidate costs .gasOnly ∅ [zero] [zero,zero] {zero}).map
  (fun result => traceCost costs result.trace) = some ⟨2,1⟩
#guard (Schedule.appendCandidate costs .gasOnly ∅ [a] [a,a,a] {a,a}).map
  (fun result => traceCost costs result.trace) = some ⟨6,2⟩
#guard (Schedule.appendCandidate costs .gasOnly {⟨0⟩} [] [a,a] {a,a}).map
  (fun result => traceCost costs result.trace) = some ⟨9,4⟩
#guard (Schedule.appendCandidate costs .gasOnly ∅ [a,b] [a,b] 0).map
  (fun result => traceCost costs result.trace) = some Cost.zero

#guard (Schedule.appendCandidate costs .gasOnly ∅ [a,b] [b,a] 0).isNone
#guard (Schedule.appendCandidate costs .gasOnly ∅
  ([a] ++ List.replicate 16 zero) ([a] ++ List.replicate 16 zero ++ [a]) {a}).isNone

-- Positive SWAP price is needed for the append-only completeness claim.
-- Here a free SWAP attains baseline0, but the source is not a target prefix.
private def freeSwapCosts : PrimitiveCosts := { costs with swap := Cost.zero }
private def freeSwap : Trace ∅ [a,b] [b,a] :=
  .Swap 1 (by decide) (by decide) (by decide) (.Lit [a,b])

example : Eligible 0 freeSwap := by constructor <;> simp [freeSwap, Trace.noPop, Trace.additions]
example : (traceCost freeSwapCosts freeSwap).score .gasOnly =
    baseline freeSwapCosts .gasOnly ∅ [a,b] 0 := by rfl
#guard (Schedule.appendCandidate freeSwapCosts .gasOnly ∅ [a,b] [b,a] 0).isNone

end OptimalityAppendTests
