import Shuffler.Optimality.ValueGraph

namespace Tests.OptimalityValueGraph

open Shuffler.Optimality

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩
private def d : Value := .Var ⟨3⟩
private def e : Value := .Var ⟨4⟩

private def swaps (source target : Stack) : Option Nat :=
  (ValueGraph.build ∅ source target).map fun result => result.trace.swapCount

#guard swaps [] [] = some 0
#guard swaps [a] [a] = some 0
#guard swaps [a, a, a] [a, a, a] = some 0
#guard swaps [a, b] [b, a] = some 1

-- The correct top occurrence joins the mismatch circuit. Keeping it fixed
-- would require three swaps; changing the equal-occurrence assignment uses two.
#guard swaps [a, b, a] [b, a, a] = some 2
#guard swaps [a, b, c] [b, a, c] = some 3
#guard swaps [a, b, c] [b, c, a] = some 2
#guard swaps [a, b, c, d, e] [b, a, d, c, e] = some 6
#guard swaps [a, b, c, d, a] [b, a, d, c, a] = some 5

-- SWAP16 can reach the oldest slot of a seventeen-slot stack.
#guard swaps ([a] ++ List.replicate 15 c ++ [b])
    ([b] ++ List.replicate 15 c ++ [a]) = some 1

-- A frozen prefix stays fixed. Equal values in it are not movable copies.
#guard swaps ([e, a] ++ List.replicate 15 c ++ [b])
    ([e, b] ++ List.replicate 15 c ++ [a]) = some 1
#guard swaps ([a, a] ++ List.replicate 15 c ++ [b])
    ([b, a] ++ List.replicate 15 c ++ [a]) = none

-- Exact order, length, and multiplicities are checked at the boundary.
#guard swaps [a, b] [a] = none
#guard swaps [a, b] [a, b, b] = none
#guard swaps [a, b] [a, c] = none
#guard swaps [a, b] [.Wildcard, b] = none

end Tests.OptimalityValueGraph
