import Shuffler.Optimality.BirthPlacement.SourceRealize.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalitySourceRealize

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def source : Stack := [.Var ⟨0⟩, .Var ⟨1⟩, .Var ⟨2⟩]
private def seed : List Op := [.dup 2, .swap 3, .dup 2, .swap 3]

-- The source has no spilled variables. Both required births come from DUP.
#guard (replay ∅ source seed).map (fun result => result.target) =
  some [.Var ⟨1⟩, .Var ⟨2⟩, .Var ⟨2⟩, .Var ⟨0⟩, .Var ⟨1⟩]
#guard (replay ∅ source seed).map (fun result =>
  (canonicalizeTraceAssignment result.built.trace result.built.noPop).built.trace.swapCount) = some 2
#guard (replay ∅ source seed).map (fun result =>
  traceEvents (canonicalizeTraceAssignment result.built.trace result.built.noPop).built.trace) =
  some [(.dup, .Var ⟨1⟩), (.dup, .Var ⟨2⟩)]
#guard (replay ∅ source seed).map (fun result =>
  (canonicalizeTraceAssignment result.built.trace result.built.noPop).built.trace.additions) =
  some ({.Var ⟨1⟩, .Var ⟨2⟩} : Multiset Value)

-- A source-only two-cycle below the top keeps its three-SWAP cost.
private def closedSeed : List Op := [.swap 2, .swap 1, .swap 2]
#guard (replay ∅ source closedSeed).map (fun result =>
  (canonicalizeTraceAssignment result.built.trace result.built.noPop).built.trace.swapCount) = some 3

-- Source length18 is supported. SWAP16 reaches position1; position0 is untouched.
private def longSource : Stack := (List.range 18).map (fun index => Value.Var ⟨index⟩)
#guard (replay ∅ longSource [.swap 16]).map (fun result =>
  flatten (canonicalizeTraceAssignment result.built.trace result.built.noPop).built.trace) =
  some [.swap 16]
#guard (replay ∅ longSource [.swap 17]).isNone
#guard (replay ∅ source [.pop]).isNone

-- The same construction also handles an empty source and no instructions.
#guard flatten (canonicalizeTraceAssignment (Trace.Lit (spills := ∅) []) trivial).built.trace = []
#guard (replay ∅ [] [.push (.Lit 7), .dup 1]).map (fun result =>
  flatten (canonicalizeTraceAssignment result.built.trace result.built.noPop).built.trace) =
  some [.push (.Lit 7), .dup 1]

-- These theorems use actual production traces and all nonnegative gas/byte weights.
example (trace : Trace spills source target) (hpop : trace.noPop) :
    (canonicalizeTraceAssignment trace hpop).built.trace.swapCount ≤ 2 * trace.swapCount :=
  canonicalizeTraceAssignment_swapCount_le_twice trace hpop

example (costs : PrimitiveCosts) (weights : Weights)
    (trace : Trace spills source target) (hpop : trace.noPop) :
    (traceCost costs (canonicalizeTraceAssignment trace hpop).built.trace).score weights -
        baseline costs weights spills source trace.additions ≤
      2 * ((traceCost costs trace).score weights -
        baseline costs weights spills source trace.additions) :=
  canonicalizeTraceAssignment_surplus_le_twice costs weights trace hpop

end Tests.OptimalitySourceRealize
