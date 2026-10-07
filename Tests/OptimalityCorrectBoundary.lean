import Shuffler.Optimality.GroupEntry.CorrectBoundary
import Shuffler.Optimality.Replay

namespace Tests.OptimalityCorrectBoundary

open Shuffler.Optimality

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def zero : Value := .Lit 0
private def initial : Stack := [zero, a] ++ List.replicate 14 zero ++ [b]
private def finalStack : Stack := [a, a] ++ List.replicate 15 zero ++ [b]
private def built := (replayExact {⟨42⟩} initial finalStack {a}
  [.swap 15, .swap 16, .load ⟨42⟩, .swap 16]).get (by decide)

#guard GroupEntry.CorrectBoundary initial finalStack {a} a
#guard (GroupEntry.checkedCorrectBoundary initial finalStack {a}).isSome
#guard (OldPositions.mismatches initial finalStack).card = 1
#guard GroupEntry.correctBoundaryBound initial finalStack {a} = 3
#guard built.trace.swapCount = 3

-- The bonus needs growth, a full window, a wrong boundary, and correct
-- source copies below top. Each failed premise disables the certificate.
#guard ¬GroupEntry.CorrectBoundary initial finalStack 0 a
#guard ¬GroupEntry.CorrectBoundary (initial.drop 1) finalStack {a} a
#guard ¬GroupEntry.CorrectBoundary finalStack finalStack {a} a
#guard ¬GroupEntry.CorrectBoundary (List.replicate 16 zero ++ [a])
  (a :: List.replicate 16 zero ++ [a]) {a} a
#guard ¬GroupEntry.CorrectBoundary initial (a :: zero :: finalStack.drop 2) {a} a
#guard GroupEntry.correctBoundaryBound [] [a] {a} = 0
#guard GroupEntry.correctBoundaryBound initial finalStack 0 = 0

example (trace : Trace {⟨42⟩} initial finalStack) (he : Eligible {a} trace) :
    3 ≤ trace.swapCount := by
  have h := GroupEntry.correctBoundaryBound_le_swapCount trace he
  have hv : GroupEntry.correctBoundaryBound initial finalStack {a} = 3 := by decide
  rwa [hv] at h

end Tests.OptimalityCorrectBoundary
