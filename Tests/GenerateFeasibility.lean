import Shuffler.BuildBottomUp.Theorems.Feasibility

open Shuffler.Generate

namespace GenerateFeasibilityTests

private def a : Value := .Var ⟨1⟩
private def b : Value := .Var ⟨2⟩

example : CanGenerate ∅ [] [] :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

-- Depth is zero at the top. DUP16 reaches depth fifteen.
private def atDepth15 : Stack := [a] ++ List.replicate 15 (.Lit 0)
private def atDepth16 : Stack := [a] ++ List.replicate 16 (.Lit 0)

example : CanGenerate ∅ atDepth15 [a] :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

example : ¬CanGenerate ∅ atDepth16 [a] := by
  rw [canGenerate_iff_ready]
  decide

-- An absent nonfree value cannot be added without a spill.
example : ¬CanGenerate ∅ [a] [b] := by
  rw [canGenerate_iff_ready]
  decide

example : ¬CanGenerate ∅ [] [a] := by
  rw [canGenerate_iff_ready]
  decide

example : CanGenerate ∅ [] [.Lit 0, .Wildcard, .Lit 37] :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

example : CanGenerate {⟨1⟩} [] [a, a] :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

example : ¬CanGenerate {⟨1⟩} [] [a, b] := by
  rw [canGenerate_iff_ready]
  decide

-- A requested value may occur more times than the DUP range contains slots.
example : CanGenerate ∅ atDepth15 (List.replicate 40 a) :=
  (canGenerate_iff_ready _ _ _).mpr (by decide)

-- The requested list specifies multiplicity, not generation order.
private def orderSource : Stack := [a, b] ++ List.replicate 14 (.Lit 0)

private def firstA : Trace ∅ orderSource (orderSource ++ [a]) :=
  .Dup 16 (by decide) (by decide) (by decide) (.Lit orderSource)

private def thenB : Trace ∅ orderSource (orderSource ++ [a, b]) :=
  .Dup 16 (by decide) (by decide) (by decide) firstA

private def thenA : Trace ∅ orderSource (orderSource ++ [a, b, a]) :=
  .Dup 2 (by decide) (by decide) (by decide) thenB

example : thenA.onlyGenerates := True.intro

-- This witness uses actual Trace constructors: DUP16, DUP16, DUP2.
example : CanGenerate ∅ orderSource [a, a, b] := by
  refine ⟨[a, b, a], ?_, thenA, ?_⟩
  · decide
  · exact True.intro

example : Ready ∅ orderSource [a, a, b] := by decide

-- Adding both copies of a first leaves b below DUP reach.
private def wrongOrder : Trace ∅ orderSource (orderSource ++ [a, a]) :=
  .Dup 1 (by decide) (by decide) (by decide) firstA

example : wrongOrder.onlyGenerates := True.intro

example : ¬CanGenerate ∅ (orderSource ++ [a, a]) [b] := by
  rw [canGenerate_iff_ready]
  decide

-- A swap or pop is outside the stated generation relation.
private def withSwap : Trace ∅ [a, b] [b, a] :=
  .Swap 1 (by decide) (by decide) (by decide) (.Lit _)

private def withPop : Trace ∅ [a] [] :=
  .Pop (by decide) (.Lit _)

example : ¬withSwap.onlyGenerates := id
example : ¬withPop.onlyGenerates := id

end GenerateFeasibilityTests
