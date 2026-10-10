import Shuffler.BuildBottomUp.Theorems.Feasibility
import Shuffler.BuildBottomUp.Theorems.Wildcard

open Shuffler.Placement

set_option maxRecDepth 16384

namespace PlacementFeasibilityTests

private instance (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    Decidable (Reserve spills source target missing) := by
  unfold Reserve
  infer_instance

private def a : Value := .Var ⟨17⟩
private def b : Value := .Var ⟨18⟩
private def others (n : Nat) : Stack := (List.range n).map (fun i => .Var ⟨i + 1⟩)

-- Empty sources allow free values, but cannot supply an unspilled variable.
example : Reserve ∅ [] [] 0 := by decide
example : CanPlace ∅ [] [] 0 :=
  (canPlace_iff_reserve _ _ _ _).mpr (by decide)
example : Reserve ∅ [] [.Lit 7] {.Lit 7} := by decide
example : CanPlace ∅ [] [.Lit 7] {.Lit 7} :=
  (canPlace_iff_reserve _ _ _ _).mpr (by decide)
example : ¬Reserve ∅ [] [a] {a} := by decide
example : ¬CanPlace ∅ [] [a] {a} := by
  rw [canPlace_iff_reserve]
  decide

-- Without POP, a nonempty source cannot become empty.
example : ¬Reserve ∅ [a] [] 0 := by decide
example : ¬CanPlace ∅ [a] [] 0 := by
  rw [canPlace_iff_reserve]
  decide

-- One occurrence cannot be both a fixed output and a retained DUP source.
private def oneSource : Stack := others 16 ++ [a]
private def oneTarget : Stack := [a] ++ others 16 ++ [a]

example : Shuffler.Generate.Ready ∅ oneSource [a] := by decide
example : ¬Reserve ∅ oneSource oneTarget {a} := by decide
example : ¬CanPlace ∅ oneSource oneTarget {a} := by
  rw [canPlace_iff_reserve]
  decide

-- Loading a removes its seed requirement, but still reserves an output copy.
example : Reserve {⟨17⟩} oneSource oneTarget {a} := by decide
example : CanPlace {⟨17⟩} oneSource oneTarget {a} :=
  (canPlace_iff_reserve _ _ _ _).mpr (by decide)

private def twoSource : Stack := [a] ++ others 15 ++ [a]
private def twoTarget : Stack := [a] ++ others 15 ++ [a, a]

example : Reserve ∅ twoSource twoTarget {a} := by decide

private def duplicateSecond : Trace ∅ twoSource twoTarget :=
  .Dup 1 (by decide) (by decide) (by decide) (.Lit twoSource)

example : CanPlace ∅ twoSource twoTarget {a} :=
  ⟨duplicateSecond, True.intro, rfl⟩

-- No boundary copy is needed for a one-slot source.
example : Reserve ∅ [a] [a, a] {a} := by decide
example : boundary [a] [a, a] {a} = 0 := by decide
example : CanPlace ∅ [a] [a, a] {a} := by
  refine ⟨.Dup 1 (by decide) (by decide) (by decide) (.Lit [a]), ?_, ?_⟩
  · exact True.intro
  · rfl

-- Repeated requests require one seed, not one initial copy per request.
example : Reserve ∅ [a] (List.replicate 41 a) (List.replicate 40 a : Multiset Value) := by
  decide
example : CanPlace ∅ [a] (List.replicate 41 a) (List.replicate 40 a : Multiset Value) :=
  (canPlace_iff_reserve _ _ _ _).mpr (by decide)

-- The concrete core uses exact additions and exact Value equality.
example : ¬Reserve ∅ [a] [a, a, a] {a} := by decide
example : ¬CanPlace ∅ [a] [a, a, a] {a} := by
  rw [canPlace_iff_reserve]
  decide
example : Reserve ∅ [a] [.Wildcard, a] {.Wildcard} := by decide
example : ¬Reserve ∅ [a] [.Wildcard, .Wildcard] {.Wildcard} := by decide

-- With no additions, a short movable suffix can be permuted behind a deep prefix.
private def fixed : Stack := List.replicate 40 (.Lit 9)

example : CanPlace ∅ (fixed ++ [a, b]) (fixed ++ [b, a]) 0 :=
  canPlace_perm_append ∅ (by decide) fixed (by decide)

private def seventeen : Stack := [a] ++ List.replicate 15 (.Lit 0) ++ [b]
private def seventeenSwapped : Stack := [b] ++ List.replicate 15 (.Lit 0) ++ [a]

example : Reserve ∅ seventeen seventeenSwapped 0 := by decide
example : CanPlace ∅ seventeen seventeenSwapped 0 := by
  simpa using canPlace_perm_of_take_eq ∅ seventeen seventeenSwapped 0
    (by decide) (by decide) (by decide)

private def eighteen : Stack := [a] ++ List.replicate 16 (.Lit 0) ++ [b]
private def eighteenSwapped : Stack := [b] ++ List.replicate 16 (.Lit 0) ++ [a]

example : ¬Reserve ∅ eighteen eighteenSwapped 0 := by decide
example : ¬CanPlace ∅ eighteen eighteenSwapped 0 := by
  rw [canPlace_iff_reserve]
  decide

-- A pattern wildcard may retain a concrete source value. Failure for the raw
-- Value.Wildcard list does not imply failure for all matching result stacks.
example : ¬Reserve ∅ [a] [.Wildcard] 0 := by decide
example : ∃ result : Stack, ∃ trace : Trace ∅ [a] result,
    trace.noPop ∧ StackMatches result [.Wildcard] :=
  (exists_matching_trace_iff_reserve _ _ _).mpr ⟨[a], 0, by decide, by decide⟩

-- Concrete pattern positions still require exact values beside the wildcard.
example : ∃ result : Stack, ∃ trace : Trace ∅ [a] result,
    trace.noPop ∧ StackMatches result [.Wildcard, .Lit 7] :=
  (exists_matching_trace_iff_reserve _ _ _).mpr ⟨[a, .Lit 7], {.Lit 7}, by decide, by decide⟩
example : ¬StackMatches [a, .Lit 8] [.Wildcard, .Lit 7] := by decide

-- The BBU gap: a real plan exists, but the supplied mapping makes BBU fail.
private def literalSource : Stack := List.replicate 16 (.Lit 0) ++ [.Lit 1]
private def literalTarget : Stack := [.Lit 1] ++ List.replicate 16 (.Lit 0) ++ [.Lit 1]

private def assignment : Mapping 17 18 where
  toFun i := some ⟨i.val + 1, by have := i.isLt; omega⟩
  invFun j := if h : 0 < j.val then some ⟨j.val - 1, by have := j.isLt; omega⟩ else none
  inv i j := by
    have := i.isLt
    have := j.isLt
    split_ifs with h
    · simp only [Option.some.injEq, Fin.ext_iff]
      omega
    · simp only [false_iff, Option.some.injEq, Fin.ext_iff]
      omega

private def literalState : Shuffler.BuildBottomUp.State literalSource literalTarget ∅ where
  planned_mapping := by simpa [literalSource, literalTarget] using assignment
  stack := literalSource
  trace := .Lit literalSource
  mapping := by simpa [literalSource, literalTarget] using assignment
  pending_generations := 1

private theorem literalState_valid : literalState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, literalState.mapping i = some j → literalState.stack[i] = literalTarget[j] := by
  decide
example : Reserve ∅ literalSource literalTarget {.Lit 1} := by decide

private def placeLiteral : Trace ∅ literalSource ([.Lit 1] ++ List.replicate 16 (.Lit 0)) :=
  .Swap 16 (by decide) (by decide) (by decide) (.Lit literalSource)

private def finishLiteral : Trace ∅ literalSource literalTarget :=
  .Push (.Lit 1) (by decide) placeLiteral

example : CanPlace ∅ literalSource literalTarget {.Lit 1} :=
  ⟨finishLiteral, True.intro, rfl⟩

example : (Shuffler.BuildBottomUp.buildBottomUp literalState literalState_valid).map
    (fun result => result.1) = .error (.blocked 1) := by native_decide

end PlacementFeasibilityTests
