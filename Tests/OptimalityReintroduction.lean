import Shuffler.Optimality.Reintroduction.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityReintroduction

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def zero : Value := .Lit 0
private def wide : Value := .Lit (2 ^ 248)
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun value => if value = zero then .push0 else .push ⟨31, by decide⟩)
  (fun _ => .push ⟨31, by decide⟩)

private def surcharge (source target : Stack) (missing : Multiset Value) (ops : List Op) : Option Nat :=
  (replayExact {⟨0⟩} source target missing ops).map
    (fun built => reintroductionSurcharge costs Weights.bytesOnly built.trace)

#guard surcharge [wide] [wide, wide] {wide} [.push wide] = some 32
#guard surcharge [wide] [wide, wide] {wide} [.dup 1] = some 0
#guard surcharge [wide, wide] [wide, wide, wide] {wide} [.push wide] = some 32
#guard surcharge [] [wide, wide] {wide, wide} [.push wide, .push wide] = some 0
#guard surcharge [a] [a, a] {a} [.load ⟨0⟩] = some 33
#guard surcharge [wide, a] [wide, a, wide, a] {wide, a} [.push wide, .load ⟨0⟩] = some 65
#guard surcharge [zero] [zero, zero] {zero} [.push zero] = some 0

-- The choice bound compares the cost of a new direct introduction with the
-- cost of carrying a retained lineage. A missing copy is required for LOAD.
#guard lineageValueBound costs Weights.bytesOnly {⟨0⟩} [a]
  (List.replicate 33 zero ++ [a]) {a} a = 2
#guard lineageValueBound costs Weights.bytesOnly {⟨0⟩} [a]
  (List.replicate 33 zero ++ [a]) 0 a = 3
#guard lineageValueBound costs Weights.bytesOnly ∅ [a]
  (List.replicate 33 zero ++ [a]) {a} a = 2

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing +
      lineageBound costs weights spills source target missing ≤ (traceCost costs trace).score weights :=
  baseline_add_lineageBound_le_score costs weights trace he

end Tests.OptimalityReintroduction
