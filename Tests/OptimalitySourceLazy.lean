import Shuffler.Optimality.BirthPlacement.SourceLazy.Build
import Shuffler.Optimality.BirthPlacement.SourceRealize
import Shuffler.Optimality.BirthPlacement.TracePlan.Extract

namespace Tests.OptimalitySourceLazy

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def c : Value := .Var ⟨44⟩

private def distinct : SourcePlan ∅ [a, b, c] [b, c, c, a, b] where
  source_length := by decide
  assignment := List.formPerm [0, 3, 4, 1]
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .dup
  available := by decide

#guard (realizeSource distinct).built.trace.swapCount = 5
#guard (SourceLazy.realize distinct).built.trace.swapCount = 3
#guard traceEvents (SourceLazy.realize distinct).built.trace = [(.dup, b), (.dup, c)]
#guard traceAssignment (SourceLazy.realize distinct).built.trace
  (SourceLazy.realize distinct).built.noPop = distinct.assignment

private def lit (i : Nat) : Value := .Lit (Fin.ofNat _ i)

private def latest : SourcePlan ∅ [lit 1, lit 2, lit 2, lit 1, lit 2]
    [lit 2, lit 1, lit 4, lit 3, lit 2, lit 1, lit 2] where
  source_length := by decide
  assignment := List.formPerm [0, 5, 3, 1, 6, 2]
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

#guard (realizeSource latest).built.trace.swapCount = 9
#guard (SourceLazy.realize latest).built.trace.swapCount = 5
#guard traceAssignment (SourceLazy.realize latest).built.trace
  (SourceLazy.realize latest).built.noPop = latest.assignment

private def lag : SourcePlan ∅ [lit 1, lit 2, lit 3, lit 4, lit 2]
    [lit 2, lit 2, lit 4, lit 2, lit 2, lit 3, lit 1] where
  source_length := by decide
  assignment := List.formPerm [0, 6, 3, 2, 5, 1]
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .dup
  available := by decide

#guard (realizeSource lag).built.trace.swapCount = 9
#guard (SourceLazy.realize lag).built.trace.swapCount = 5
#guard traceEvents (SourceLazy.realize lag).built.trace = [(.dup, lit 2), (.dup, lit 2)]

-- Scale the reach-two boundary example by eight. Its earliest future
-- cycle vertex is 24, after position zero freezes at top16.
private def forcedAssignment : Equiv.Perm (Fin 25) := List.formPerm [0, 24, 8]
private def forcedSource : Stack := List.ofFn fun i : Fin 17 => lit i.val
private def forcedTarget : Stack := List.ofFn fun i : Fin 25 => lit (forcedAssignment.symm i).val

private def forced : SourcePlan ∅ forcedSource forcedTarget where
  source_length := by decide
  assignment := forcedAssignment
  source_values := by decide
  deadlines := by
    change ∀ i : Fin 25, i.val ≤ (forcedAssignment i).val + 16
    decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

#guard (SourceLazy.forcedCycles 16 17 forced.assignment).card = 1
#guard forced.assignment.support.card = 3
#guard (SourceLazy.realize forced).built.trace.swapCount = 4
#guard traceAssignment (SourceLazy.realize forced).built.trace
  (SourceLazy.realize forced).built.noPop = forced.assignment

private def closed : SourcePlan ∅ [a, b, c] [b, a, c] where
  source_length := by decide
  assignment := Equiv.swap 0 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

#guard (SourceLazy.realize closed).built.trace.swapCount = 3
#guard traceEvents (SourceLazy.realize closed).built.trace = []

private def empty : SourcePlan ∅ [] [] where
  source_length := by decide
  assignment := 1
  source_values := by decide
  deadlines := by decide
  source_frozen := by decide
  method := fun _ => .direct
  available := by decide

#guard (SourceLazy.realize empty).built.trace.swapCount = 0

#print axioms SourceLazy.realize

end Tests.OptimalitySourceLazy
