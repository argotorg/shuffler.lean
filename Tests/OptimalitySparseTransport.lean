import Shuffler.Optimality.Transport.Sparse.FreshSuffix

namespace Tests.OptimalitySparseTransport

open Shuffler.Optimality
open Shuffler.Optimality.Transport

private def zero : Value := .Lit 0
private def one : Value := .Lit 1
private def source (q : Nat) : Stack := List.replicate q zero
private def target (q m : Nat) : Stack := List.replicate m one ++ source q

-- A SWAP can move sixteen positions, but each of four old copies must move.
#guard requiredSwaps zero (source 4) (target 4 8) = 2
#guard sparseRequiredSwaps zero (source 4) (target 4 8) = 4
#guard requiredSwaps zero (source 8) (target 8 8) = 4
#guard sparseRequiredSwaps zero (source 8) (target 8 8) = 8
#guard sparseRequiredSwaps zero (source 15) (target 15 18) = 17
#guard sparseRequiredSwaps zero (source 16) (target 16 17) = 17
#guard sparseRequiredSwaps zero (source 0) (target 0 33) = 0
#guard sparseRequiredSwaps zero (source 16) (target 16 0) = 0

-- The formula covers empty sources, all working-window sizes, and two wraps.
#guard ∀ q : Fin 17, ∀ m : Fin 34,
  sparseRequiredSwaps zero (source q.val) (target q.val m.val) =
    q.val * (m.val / 16) + min q.val (m.val % 16)

example (trace : Trace spills (source 4) (target 4 8)) (hpop : trace.noPop) :
    4 ≤ Lineage.upwardCount zero trace := by
  dsimp only [source, target] at trace hpop ⊢
  have h := fresh_suffix_old_swaps_le zero (List.replicate 8 one) (by decide) 4 (by decide) trace hpop
  have hv : 4 * ((List.replicate 8 one).length / 16) +
      min 4 ((List.replicate 8 one).length % 16) = 4 := by decide
  omega

example (trace : Trace spills (source 15) (target 15 33)) (hpop : trace.noPop) :
    31 ≤ Lineage.upwardCount zero trace := by
  dsimp only [source, target] at trace hpop ⊢
  have h := fresh_suffix_old_swaps_le zero (List.replicate 33 one) (by decide) 15 (by decide) trace hpop
  have hv : 15 * ((List.replicate 33 one).length / 16) +
      min 15 ((List.replicate 33 one).length % 16) = 31 := by decide
  omega

example (value : Value) (trace : Trace spills before after) (hpop : trace.noPop) :
    sparseRequiredSwaps value before after ≤ Lineage.upwardCount value trace :=
  sparseRequiredSwaps_le_upwardCount value trace hpop

end Tests.OptimalitySparseTransport
