import Shuffler.Optimality.Collective.InventoryBound.Theorems

namespace Tests.OptimalityInventoryBound

open Shuffler.Optimality Shuffler.Optimality.Collective

set_option maxRecDepth 8192

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩, ⟨43⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)
private def premium (value : Value) : Nat :=
  directPrice costs .bytesOnly spills value - unitPrice costs .bytesOnly spills value
private def old : Stack := List.replicate 15 zero
private def target : Stack := [a, b, a, b] ++ old

#guard premium a = 33
#guard (paidIntervals old target).card = 2
#guard intervalWeight premium (paidIntervals old target) = 66
#guard inventoryMaximum old target premium = 33
#guard inventoryFloor old target premium = 33
#guard ¬FeasiblePaidIntervals old target (paidIntervals old target)
#guard FeasiblePaidIntervals old target ∅
#guard inventoryMaximum old target (fun _ => 0) = 0
#guard inventoryFloor old ([a, b, a, b, a, b] ++ old) premium = 66

-- Consuming one old copy first leaves two seed slots for the overlapping gaps.
private def consumeOld : Stack := [zero, a, b, a, b] ++ List.replicate 14 zero
#guard inventoryMaximum old consumeOld premium = 66
#guard inventoryFloor old consumeOld premium = 0

-- Once the one old a is output, its later reuse interval is paid too.
private def oldA : Stack := a :: old
#guard (paidIntervals oldA target).card = 2
#guard inventoryMaximum oldA target premium = 33
#guard inventoryFloor oldA target premium = 33

-- Sixteen mandatory copies leave no seed slot.
private def full : Stack := List.replicate 16 zero
#guard inventoryMaximum full ([a, a] ++ full) premium = 0
#guard inventoryFloor full ([a, a] ++ full) premium = 33

-- A zero saved-weight maximum does not certify feasibility of the state.
private def tooFull : Stack := List.replicate 17 zero
#guard ¬FeasiblePaidIntervals tooFull (a :: tooFull) ∅
#guard inventoryMaximum [] [] premium = 0
#guard inventoryFloor [] [] premium = 0

example (trace : Trace spills old target) (hpop : trace.noPop) :
    33 ≤ generationSurcharge costs .bytesOnly target.toFinset trace := by
  have h := inventoryFloor_le_generationSurcharge costs .bytesOnly trace hpop (by decide)
  have hf : inventoryFloor old target premium = 33 := by decide
  change inventoryFloor old target premium ≤ _ at h
  rwa [hf] at h

example (trace : Trace spills oldA target) (hpop : trace.noPop) :
    33 ≤ generationSurcharge costs .bytesOnly target.toFinset trace := by
  have h := inventoryFloor_le_generationSurcharge costs .bytesOnly trace hpop (by decide)
  have hf : inventoryFloor oldA target premium = 33 := by decide
  change inventoryFloor oldA target premium ≤ _ at h
  rwa [hf] at h

example (trace : Trace spills old target) (he : Eligible {a, b, a, b} trace) :
    baseline costs .bytesOnly spills old {a, b, a, b} + trace.swapCount + 33 ≤
      (traceCost costs trace).score .bytesOnly := by
  have h := baseline_add_swapCost_add_inventoryFloor_le_score_of_eligible
    costs .bytesOnly trace he (by decide)
  have hf : inventoryFloor old target premium = 33 := by decide
  change baseline costs .bytesOnly spills old {a, b, a, b} + 1 * trace.swapCount +
    inventoryFloor old target premium ≤ _ at h
  simpa only [hf, Nat.one_mul] using h

end Tests.OptimalityInventoryBound
