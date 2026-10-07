import Shuffler.Optimality.GenerationSurcharge.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityGenerationSurcharge

open Shuffler.Optimality

private def wide : Value := .Lit (2 ^ 248)
private def a : Value := .Var ⟨0⟩
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push ⟨31, by decide⟩) (fun _ => .push0)

private def surcharge (values : Finset Value) (source target : Stack)
    (missing : Multiset Value) (ops : List Op) : Option Nat :=
  (replayExact {⟨0⟩} source target missing ops).map
    (fun built => generationSurcharge costs Weights.bytesOnly values built.trace)

#guard surcharge {wide} [] [wide] {wide} [.push wide] = some 0
#guard surcharge {wide} [] [wide, wide] {wide, wide} [.push wide, .push wide] = some 32
#guard surcharge {wide} [] [wide, wide] {wide, wide} [.push wide, .dup 1] = some 0
#guard surcharge {wide} [wide] [wide, wide, wide] {wide, wide} [.push wide, .push wide] = some 64
#guard surcharge ∅ [] [wide, wide] {wide, wide} [.push wide, .push wide] = some 0
#guard surcharge {a} [] [a, a, a] {a, a, a} [.load ⟨0⟩, .load ⟨0⟩, .load ⟨0⟩] = some 2
#guard surcharge {a} [] [a, a, a] {a, a, a} [.load ⟨0⟩, .dup 1, .dup 1] = some 0

example (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + costs.swap.score weights * trace.swapCount +
      generationSurcharge costs weights values trace ≤ (traceCost costs trace).score weights :=
  baseline_add_swapCost_add_generationSurcharge_le_score_of_eligible costs weights values trace he

end Tests.OptimalityGenerationSurcharge
