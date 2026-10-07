import Shuffler.Optimality.Cost
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
A lower bound on the cost of generating the exact additions. Each occurrence
costs at least the smaller of DUP and direct generation. A value absent from
the source needs one direct introduction. This bound ignores stack depth and
placement. Its proof is in `Baseline.Theorems`.
-/

namespace Shuffler.Optimality

-- Values without PUSH or LOAD use DUP as a finite fallback. A valid trace
-- cannot introduce an absent value of this kind.
def directPrice (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) : Value → Nat
  | .Lit value => (costs.push (.Lit value)).score weights
  | .Wildcard => (costs.push .Wildcard).score weights
  | .Var id => if id ∈ spills then (costs.load id).score weights else costs.dup.score weights
  | .FunctionReturnLabel => costs.dup.score weights

def unitPrice (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (value : Value) : Nat :=
  min (costs.dup.score weights) (directPrice costs weights spills value)

def baseline (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source : Stack) (missing : Multiset Value) : Nat :=
  (missing.map (unitPrice costs weights spills)).sum +
    missing.toFinset.sum (fun value =>
      if value ∈ source then 0
      else directPrice costs weights spills value - unitPrice costs weights spills value)

end Shuffler.Optimality
