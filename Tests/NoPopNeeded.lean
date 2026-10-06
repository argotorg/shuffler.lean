import Shuffler.Placement.NoPopNeeded

open Shuffler.Placement

namespace NoPopNeededTests

private def x : Value := .Var ⟨42⟩
private def zero : Value := .Lit 0

example : NoPopNeeded ∅ [] [] := by unfold NoPopNeeded Reserve; decide
example : NoPopNeeded ∅ [x] [x, x] := by unfold NoPopNeeded Reserve; decide
example : ∃ trace : Trace ∅ [x] [x, x], trace.noPop :=
  (noPopNeeded_iff_exists_trace _ _ _).mp (by unfold NoPopNeeded Reserve; decide)

-- Truncated subtraction does not hide the removal of a source value.
example : ¬NoPopNeeded ∅ [x] [] := by unfold NoPopNeeded Reserve; decide
example : ¬NoPopNeeded ∅ [x] [zero] := by unfold NoPopNeeded Reserve; decide

-- Failure of the condition can also mean that no trace exists at all.
example : ¬NoPopNeeded ∅ [] [x] := by unfold NoPopNeeded Reserve; decide

-- Here POP does make a difference: it exposes x for the next swap.
private def source : Stack := [x] ++ List.replicate 17 zero
private def target : Stack := [zero, x] ++ List.replicate 17 zero
private def removed : Trace ∅ source ([x] ++ List.replicate 16 zero) :=
  .Pop (by decide) (.Lit source)
private def raised : Trace ∅ source (List.replicate 16 zero ++ [x]) :=
  .Swap 16 (by decide) (by decide) (by decide) removed
private def placed : Trace ∅ source ([zero, x] ++ List.replicate 15 zero) :=
  .Swap 15 (by decide) (by decide) (by decide) raised
private def replaced : Trace ∅ source ([zero, x] ++ List.replicate 16 zero) :=
  .Push zero (by decide) placed
private def finished : Trace ∅ source target := .Push zero (by decide) replaced

example : ¬NoPopNeeded ∅ source target := by unfold NoPopNeeded Reserve; decide
example : ¬∃ trace : Trace ∅ source target, trace.noPop := by
  rw [← noPopNeeded_iff_exists_trace]
  unfold NoPopNeeded Reserve
  decide
example : finished.additions = {zero, zero} := rfl
example : ¬finished.noPop := by change ¬False; exact not_false

end NoPopNeededTests
