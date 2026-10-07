import Shuffler.Optimality.Approximation.Build
import Shuffler.Optimality.Replay

namespace Tests.OptimalityApproximation

open Shuffler.Optimality

set_option maxRecDepth 8192

private def a : Value := .Var ⟨0⟩
private def b : Value := .Var ⟨1⟩
private def c : Value := .Var ⟨2⟩
private def zero : Value := .Lit 0
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push0)

private def checked (source target : Stack) (missing : Multiset Value) (ops : List Op) : Bool :=
  match replayExact ∅ source target missing ops with
  | none => false
  | some built => (certifyTwiceLineage costs Weights.bytesOnly built).isSome

#guard checked [] [] 0 []
#guard checked [] [zero] {zero} [.push zero]
#guard checked [a] [a, a] {a} [.dup 1]
#guard checked [a, b] [a, b] 0 []
-- OPT equals B=0. A factor on total cost must not hide excess above zero.
#guard !checked [a, b] [a, b] 0 [.swap 1, .swap 1]
#guard checked [a, b] [b, a] 0 [.swap 1]
-- A false result can mean the static bound is too weak: this three-SWAP trace
-- is optimal, while the lineage distance bound is only one for this input.
#guard !checked [a, b, c] [b, a, c] 0 [.swap 2, .swap 1, .swap 2]

private def checkedStatic (source target : Stack) (missing : Multiset Value) (ops : List Op) : Bool :=
  match replayExact ∅ source target missing ops with
  | none => false
  | some built => (certifyTwiceStatic costs Weights.bytesOnly built).isSome

-- The old-position count certifies this case that the lineage bound misses.
#guard checkedStatic [a, b, c] [b, a, c] 0 [.swap 2, .swap 1, .swap 2]
#guard checkedStatic [a, b, c] [b, a, c] 0 [.swap 2, .swap 1, .swap 2, .swap 1, .swap 1]
#guard !checkedStatic [a, b, c] [b, a, c] 0
  [.swap 2, .swap 1, .swap 2, .swap 1, .swap 1, .swap 1, .swap 1]
#guard !checkedStatic [a, b] [a, b] 0 [.swap 1, .swap 1]
-- Only the initial top is wrong; the requested DUP makes lineage distance zero.
#guard checkedStatic [a] [zero, a, a] {zero, a} [.dup 1, .push zero, .swap 2]
-- The old-top cut requires two swaps. Four swaps meet the factor-two bound.
#guard staticExcess costs Weights.bytesOnly ∅ [a, b] [zero, a, b] {zero} = 2
#guard checkedStatic [a, b] [zero, a, b] {zero}
  [.swap 1, .push zero, .swap 2, .swap 1, .swap 1]
#guard !checkedStatic [a, b] [zero, a, b] {zero}
  [.swap 1, .push zero, .swap 2, .swap 1, .swap 1, .swap 1, .swap 1]

private def source : Stack := a :: List.replicate 15 zero
private def target : Stack := source ++ List.replicate 17 zero ++ [a]
private def missing : Multiset Value := {a} + Multiset.replicate 17 zero
private def carryOps : List Op :=
  [.dup 16] ++ List.replicate 16 (.push zero) ++ [.swap 16, .push zero, .swap 1]

-- B=18 bytes and the proved excess lower bound is two bytes. The first
-- trace attains the bound. Two redundant swaps attain the factor-two limit.
#guard checked source target missing carryOps
#guard checked source target missing (carryOps ++ [.swap 1, .swap 1])
#guard !checked source target missing (carryOps ++ [.swap 1, .swap 1, .swap 1, .swap 1])

private def twiceCarry :=
  (replayExact ∅ source target missing (carryOps ++ [.swap 1, .swap 1])).get (by decide)
private def certified :=
  (certifyTwiceLineage costs Weights.bytesOnly twiceCarry).get (by decide)

-- The returned certificate compares to every legal production trace with
-- the exact same endpoint and exact additions, without an oracle search.
example (other : Trace ∅ source target) (he : Eligible missing other) :
    (traceCost costs certified.built.trace).bytes + baseline costs Weights.bytesOnly ∅ source missing ≤
      2 * (traceCost costs other).bytes := by
  simpa only [Cost.score_bytesOnly] using certified.guarantee.2 other he

example (trace : Trace spills start finish) :
    TwiceExcess costs weights additions trace ↔
      Eligible additions trace ∧ ∀ other : Trace spills start finish, Eligible additions other →
        (traceCost costs trace).score weights - baseline costs weights spills start additions ≤
          2 * ((traceCost costs other).score weights - baseline costs weights spills start additions) :=
  twiceExcess_iff_sub costs weights trace

end Tests.OptimalityApproximation
