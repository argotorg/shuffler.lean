import Shuffler.Optimality.Cost
import Mathlib.Data.Finset.Card

namespace Shuffler.Optimality.GroupEntry

-- Count lower-slot selections in a fixed set of absolute stack positions.
def selections (positions : Finset Nat) : Trace spills source target → Nat
  | .Lit _ => 0
  | @Trace.Swap _ _ previous depth _ _ _ trace =>
      selections positions trace + if previous.length - 1 - depth ∈ positions then 1 else 0
  | .Dup _ _ _ _ trace => selections positions trace
  | .Pop _ trace => selections positions trace
  | .Push _ _ trace => selections positions trace
  | .Load _ _ trace => selections positions trace

def differences (positions : Finset Nat) (wanted current : Stack) : Finset Nat :=
  positions.filter fun i => wanted[i]? ≠ current[i]?

end Shuffler.Optimality.GroupEntry
