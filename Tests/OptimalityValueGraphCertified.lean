import Shuffler.Optimality.ValueGraph.CertifiedComplete

namespace Tests.OptimalityValueGraphCertified

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩
private def d : Value := .Var ⟨3⟩
private def e : Value := .Var ⟨4⟩

-- Each successful call contains a proof against all legal no-POP traces with
-- no additions, not only against traces produced by this planner.
private def certified (source target : Stack) : Bool :=
  (ValueGraph.buildCertified ∅ source target).isSome

#guard certified [] []
#guard certified [a] [a]
#guard certified [a, a, a] [a, a, a]
#guard certified [a, b] [b, a]
#guard certified [a, b, a] [b, a, a]
#guard certified [a, b, c] [b, a, c]
#guard certified [a, b, c] [b, c, a]
#guard certified [a, b, c, d, e] [b, a, d, c, e]
#guard certified [a, b, c, d, a] [b, a, d, c, a]
#guard certified ([a] ++ List.replicate 15 c ++ [b])
    ([b] ++ List.replicate 15 c ++ [a])
#guard certified ([e, a] ++ List.replicate 15 c ++ [b])
    ([e, b] ++ List.replicate 15 c ++ [a])
#guard !(certified ([a, a] ++ List.replicate 15 c ++ [b])
    ([b, a] ++ List.replicate 15 c ++ [a]))
#guard !(certified [a, b] [a])
#guard !(certified [a, b] [a, b, b])
#guard !(certified [a, b] [a, c])

example (result : ValueGraph.OptimalTrace spills source target)
    (costs : PrimitiveCosts) (weights : Weights) :
    WeightedOptimal costs weights 0 result.built.trace :=
  result.weightedOptimal costs weights

-- This checks the public success contract for every input, including a frozen
-- prefix. The proof does not depend on the finite examples above.
example (spills : SpillSet) (source target : Stack) :
    (ValueGraph.buildCertified spills source target).isSome ↔
      Shuffler.Placement.Reserve spills source target 0 :=
  ValueGraph.buildCertified_succeeds_iff_reserve spills source target

end Tests.OptimalityValueGraphCertified
