import Shuffler.Optimality.BirthPlacement.SourceCheapest.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalitySourceCheapest

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def value : Value := .Var ⟨42⟩
private def spills : SpillSet := {⟨42⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm (fun _ => .push0) (fun _ => .push0)

-- An initial source copy can replace a repeated LOAD with DUP.
#guard (replay spills [value] [.load ⟨42⟩]).map (fun result =>
  flatten (optimizeTraceAssignment costs .gasOnly result.built.trace result.built.noPop).built.trace) =
  some [.dup 1]
#guard (replay spills [value] [.load ⟨42⟩]).map (fun result =>
  flatten (optimizeTraceAssignment costs .bytesOnly result.built.trace result.built.noPop).built.trace) =
  some [.dup 1]

-- PUSH0 is cheaper than DUP in gas, even with a source copy available.
#guard (replay ∅ [.Lit 0] [.dup 1]).map (fun result =>
  flatten (optimizeTraceAssignment costs .gasOnly result.built.trace result.built.noPop).built.trace) =
  some [.push (.Lit 0)]

-- Absolute source height controls DUP availability. DUP16 is allowed; DUP17 is not.
private def source16 : Stack := value :: List.replicate 15 (.Lit 0)
private def source17 : Stack := value :: List.replicate 16 (.Lit 0)
#guard (replay spills source16 [.load ⟨42⟩]).map (fun result =>
  flatten (optimizeTraceAssignment costs .gasOnly result.built.trace result.built.noPop).built.trace) =
  some [.dup 16]
#guard (replay spills source17 [.load ⟨42⟩]).map (fun result =>
  flatten (optimizeTraceAssignment costs .gasOnly result.built.trace result.built.noPop).built.trace) =
  some [.load ⟨42⟩]
#guard (replay spills source17 [.dup 17]).isNone

-- The comparison now permits different LOAD/DUP choices in the other trace.
example (costs : PrimitiveCosts) (weights : Weights)
    (seed other : Trace spills source target) (hseed : seed.noPop) (hother : other.noPop)
    (hassignment : traceAssignment seed hseed = traceAssignment other hother) :
    (traceCost costs (optimizeTraceAssignment costs weights seed hseed).built.trace).score weights -
        baseline costs weights spills source other.additions ≤
      2 * ((traceCost costs other).score weights -
        baseline costs weights spills source other.additions) :=
  optimizeTraceAssignment_surplus_le_twice costs weights seed other hseed hother hassignment

end Tests.OptimalitySourceCheapest
