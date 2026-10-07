import Shuffler.Optimality.ValueAccounting.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityGapTail

open Shuffler.Optimality

private def a : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm (fun _ => .push0) (fun _ => .push0)
private def source : Stack := List.replicate 15 zero ++ [a]
private def target : Stack := a :: List.replicate 16 zero ++ [a]
private def missing : Multiset Value := {zero, a}
private def built := (replayExact spills source target missing
  [.dup 1, .swap 16, .push zero, .swap 2]).get (by decide)

-- The first copy moves downward while the final copies become separated.
#guard GapCost.valueBound costs Weights.bytesOnly spills source target a = 0
#guard GapCost.tailValueBound costs Weights.bytesOnly spills source target a = 1
#guard ValueAccounting.bound costs Weights.bytesOnly spills source target missing = 2
#guard baseline costs Weights.bytesOnly spills source missing = 2
#guard (traceCost costs built.trace).bytes = 4

-- A single copy has no gap. The original term still pays for its position.
#guard GapCost.tailValueBound costs Weights.bytesOnly spills [a] (List.replicate 16 zero ++ [a]) a = 0
#guard GapCost.valueBound costs Weights.bytesOnly spills [a] (List.replicate 16 zero ++ [a]) a = 1

example (trace : Trace spills source target) (he : Eligible missing trace) :
    4 ≤ (traceCost costs trace).score Weights.bytesOnly := by
  have h := ValueAccounting.baseline_add_bound_le_score costs Weights.bytesOnly trace he
  change 2 + 2 ≤ _ at h
  exact h

private def wideCosts : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)
private def zeros : Stack := List.replicate 16 zero
private def prefixTarget : Stack := [a, a, a] ++ zeros

-- The first absent-value introduction belongs to B. Two further LOADs cost
-- 33 extra bytes each, and the old zeros need three upward SWAPs.
#guard ValueAccounting.requiredDirect zeros prefixTarget {a, a, a} a = 3
#guard ValueAccounting.forcedPremium wideCosts Weights.bytesOnly spills zeros prefixTarget {a, a, a} a = 66
#guard ValueAccounting.bound wideCosts Weights.bytesOnly spills zeros prefixTarget {a, a, a} = 69
#guard baseline wideCosts Weights.bytesOnly spills zeros {a, a, a} = 36

-- An initial a pays for one output copy, but each requested copy still needs
-- a direct introduction while all sixteen old zeros remain above it.
#guard ValueAccounting.requiredDirect (a :: zeros) prefixTarget {a, a} a = 2
#guard ValueAccounting.bound wideCosts Weights.bytesOnly spills (a :: zeros) prefixTarget {a, a} = 68

-- Fifteen old zeroes leave room for a retained a seed.
#guard ValueAccounting.forcedPremium wideCosts Weights.bytesOnly spills
  (List.replicate 15 zero) ([a, a, a] ++ List.replicate 15 zero) {a, a, a} a = 0

example (trace : Trace spills zeros prefixTarget) (he : Eligible {a, a, a} trace) :
    105 ≤ (traceCost wideCosts trace).score Weights.bytesOnly := by
  have h := ValueAccounting.baseline_add_bound_le_score wideCosts Weights.bytesOnly trace he
  change 36 + 69 ≤ _ at h
  exact h

end Tests.OptimalityGapTail
