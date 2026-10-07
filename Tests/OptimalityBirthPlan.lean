import Shuffler.Optimality.BirthPlacement.Realize.Theorems
import Shuffler.Optimality.Replay
import Mathlib.GroupTheory.Perm.List

namespace Tests.OptimalityBirthPlan

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 10
private def b : Value := .Lit 11
private def c : Value := .Lit 12

private def empty : Plan ∅ [] where
  assignment := 1
  method := fun _ => .direct
  deadlines := by intro index; exact Fin.elim0 index
  available := by intro index; exact Fin.elim0 index

#guard flatten (realize empty).built.trace = []

private def repeatedTarget : Stack := [a, b, a]
private def repeated : Plan ∅ repeatedTarget where
  assignment := Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩
  method := fun index => if index.val = 1 then .dup else .direct
  deadlines := by decide
  available := by decide

#guard birthWord repeatedTarget repeated.assignment = [a, a, b]
#guard flatten (realize repeated).built.trace = [.push a, .dup 1, .push b, .swap 1]
#guard (replay ∅ [] (flatten (realize repeated).built.trace)).map (·.target) = some repeatedTarget

private def cycleTarget : Stack := [a, b, c]
private def cycle : Plan ∅ cycleTarget where
  assignment := List.formPerm [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

-- One birth can resolve more than one pending position.
#guard flatten (realize cycle).built.trace = [.push b, .push c, .push a, .swap 2, .swap 1]
#guard (realize cycle).built.trace.swapCount = 2

private def swapBoundaryTarget : Stack := [b] ++ List.replicate 17 a
private def swapBoundary : Plan ∅ swapBoundaryTarget where
  assignment := Equiv.swap ⟨0, by decide⟩ ⟨16, by decide⟩
  method := fun _ => .direct
  deadlines := by decide
  available := by decide

#guard (flatten (realize swapBoundary).built.trace).contains (.swap 16)
#guard (realize swapBoundary).built.trace.swapCount = 1
#guard ¬BirthDeadlines 16 (Equiv.swap (0 : Fin 18) 17)

private def dupBoundaryTarget : Stack := [a] ++ List.replicate 16 b ++ [a]
private def dupBoundary : Plan ∅ dupBoundaryTarget where
  assignment := Equiv.swap ⟨16, by decide⟩ ⟨17, by decide⟩
  method := fun index => if index.val = 16 then .dup else .direct
  deadlines := by decide
  available := by decide

#guard (flatten (realize dupBoundary).built.trace).contains (.dup 16)
#guard (flatten (realize dupBoundary).built.trace).getLast? = some (.swap 1)
#guard (replay ∅ [] (flatten (realize dupBoundary).built.trace)).map (·.target) = some dupBoundaryTarget

-- The original order needs DUP17, and so it does not meet the count condition.
#guard ¬BirthAvailable ∅ dupBoundaryTarget dupBoundaryTarget 17 a .dup
#guard ¬BirthAvailable ∅ [a] [a] 0 a .dup
#guard ¬BirthAvailable ∅ [.FunctionReturnLabel] [.FunctionReturnLabel] 0 .FunctionReturnLabel .direct

private def spilled : SpillSet := {⟨42⟩}
private def spilledValue : Value := .Var ⟨42⟩
private def loaded : Plan spilled [spilledValue, spilledValue] where
  assignment := 1
  method := fun index => if index.val = 0 then .direct else .dup
  deadlines := by decide
  available := by decide

#guard flatten (realize loaded).built.trace = [.load ⟨42⟩, .dup 1]
#guard ¬BirthAvailable ∅ [spilledValue] [spilledValue] 0 spilledValue .direct

private def wildcard : Plan ∅ [.Wildcard, .Wildcard] where
  assignment := 1
  method := fun index => if index.val = 0 then .direct else .dup
  deadlines := by decide
  available := by decide

#guard flatten (realize wildcard).built.trace = [.push .Wildcard, .dup 1]

example (plan : Plan spills target) : (realize plan).built.trace.noPop := (realize plan).built.noPop
example (plan : Plan spills target) :
    (realize plan).built.trace.swapCount ≤ plan.assignment.support.card := realize_swapCount_le_moved plan

example (plan : Plan spills target) :
    SwapRuns.births (realize plan).built.trace = birthWord target plan.assignment := realize_births plan

private def zero : Value := .Lit 0
private def zeros : Plan ∅ [zero, zero] where
  assignment := 1
  method := fun index => if index.val = 0 then .direct else .dup
  deadlines := by decide
  available := by decide

private def cheapCosts : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)
private def wideCosts : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨31, by decide⟩) (fun _ => .push ⟨31, by decide⟩)

#guard traceEvents (realize zeros).built.trace = [(.direct, zero), (.dup, zero)]
#guard flatten (realize (zeros.cheapest cheapCosts .gasOnly)).built.trace = [.push zero, .push zero]
#guard (traceCost cheapCosts (realize zeros).built.trace).gas = 5
#guard (traceCost cheapCosts (realize (zeros.cheapest cheapCosts .gasOnly)).built.trace).gas = 4

-- A tie in weighted gas can select a wider direct instruction.
#guard (traceCost wideCosts (realize zeros).built.trace).bytes = 34
#guard (traceCost wideCosts (realize (zeros.cheapest wideCosts .gasOnly)).built.trace).bytes = 66
#guard flatten (realize (zeros.cheapest wideCosts .bytesOnly)).built.trace = [.push zero, .dup 1]

example (costs : PrimitiveCosts) (weights : Weights) (plan : Plan spills target) :
    (traceCost costs (realize (plan.cheapest costs weights)).built.trace).score weights ≤
      (traceCost costs (realize plan).built.trace).score weights :=
  realize_cheapest_score_le costs weights plan

end Tests.OptimalityBirthPlan
