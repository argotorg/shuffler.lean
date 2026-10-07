import Shuffler.Optimality.BirthPlacement.SourceRealize
import Shuffler.Optimality.SwapRuns.Theorems

namespace Tests.OptimalitySourceNormalization

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 1
private def b : Value := .Lit 2
private def c : Value := .Lit 3
private def d : Value := .Lit 4

private def latest : SourcePlan ∅ [a, b, b, a, b] [b, a, d, c, b, a, b] where
  source_length := by decide
  assignment := List.formPerm [0, 5, 3, 1, 6, 2]
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

private def lag : SourcePlan ∅ [a, b, c, d, b] [b, b, d, b, b, c, a] where
  source_length := by decide
  assignment := List.formPerm [0, 6, 3, 2, 5, 1]
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .dup
  available := by decide

-- Total SWAPs, labelled entry SWAPs, value entry SWAPs, normalized total.
private def counts (plan : SourcePlan spills source target) : Nat × Nat × Nat × Nat :=
  let entry := (SourceEntry.build plan).built
  let trace := (realizeSource plan).built.trace
  (trace.swapCount, entry.trace.swapCount, (SwapRuns.improve entry).trace.swapCount,
    (SwapRuns.normalize trace).swapCount)

-- Both examples have repeated source values. Their labelled entry costs
-- exceed the costs required to reach the same concrete value stack.
#guard counts latest = (9, 6, 4, 7)
#guard counts lag = (9, 6, 5, 8)

private def comparisonCount (source target births : Stack) (ops : List Op) : Option Nat := do
  let result ← replayExact ∅ source target births ops
  return result.trace.swapCount

#guard comparisonCount [a, b, b, a, b] [b, a, d, c, b, a, b] [c, d]
  [.swap 4, .swap 3, .push c, .swap 2, .push d, .swap 4] = some 4
#guard comparisonCount [a, b, c, d, b] [b, b, d, b, b, c, a] [b, b]
  [.swap 4, .dup 4, .swap 2, .swap 3, .dup 3, .swap 2] = some 4

private def va : Value := .Var ⟨42⟩
private def vb : Value := .Var ⟨43⟩
private def vc : Value := .Var ⟨44⟩

private def distinct := (replayExact ∅ [va, vb, vc] [vb, vc, vc, va, vb]
  ([vb, vc] : Multiset Value)
  [.swap 1, .swap 2, .swap 1, .dup 3, .dup 2, .swap 3, .swap 1]).get (by decide)

-- Distinct source values remove the label issue. Both SWAP runs are
-- already minimum for their concrete endpoints. Interleaving births
-- differently is still needed to attain the two-SWAP comparison.
#guard distinct.trace.swapCount = 5
#guard (SwapRuns.normalize distinct.trace).swapCount = 5
#guard comparisonCount [va, vb, vc] [vb, vc, vc, va, vb] [vb, vc]
  [.dup 2, .swap 3, .dup 2, .swap 3] = some 2

end Tests.OptimalitySourceNormalization
