import Shuffler.ExactBuild.Build
import Shuffler.BuildBottomUp.Theorems.Complete
import Tests.BuildBottomUpObservations

open Shuffler.Placement Shuffler.ExactBuild Shuffler.BuildBottomUp BuildBottomUpTestSupport

set_option maxRecDepth 16384

namespace BuildBottomUpCompleteTests

private def a : Value := .Var ⟨42⟩
private def b : Value := .Var ⟨43⟩
private def zero : Value := .Lit 0
private def one : Value := .Lit 1

-- Inspect the generated production trace, not only the success flag.
private def checkedBuild (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) : Bool :=
  (build spills source target missing).any fun built =>
    decide (built.trace.additions = missing) &&
      (operations built.trace).all (fun op => match op with | .pop => false | _ => true)

private def checkedAdapter (state : State source target spills) (expected : Stack) : Bool :=
  (buildComplete state).any fun result => decide (result.1 = expected)

-- build finds a trace exactly when a trace without POP and with these additions exists.
example (spills : SpillSet) (source target : Stack) (missing : Multiset Value) :
    (build spills source target missing).isSome ↔ CanPlace spills source target missing :=
  build_succeeds_iff_canPlace spills source target missing

-- All stacks of up to three slots over two values, with the additions from counts.
private def small : List Stack :=
  [0, 1, 2, 3].flatMap fun n => (List.range (2 ^ n)).map fun bits =>
    (List.range n).map fun i => if bits.testBit i then a else zero

#guard small.length = 15

-- The trace checks run on every input where Reserve holds.
#guard small.all fun source => small.all fun target =>
  let missing := (target : Multiset Value) - (source : Multiset Value)
  (build ∅ source target missing).isSome = decide (Reserve ∅ source target missing) &&
    (checkedBuild ∅ source target missing = decide (Reserve ∅ source target missing))

private def shiftedMapping (n gap : Nat) : Mapping n (n + gap) where
  toFun i := some ⟨i.val + gap, by have := i.isLt; omega⟩
  invFun j := if h : gap ≤ j.val then some ⟨j.val - gap, by have := j.isLt; omega⟩ else none
  inv i j := by
    have := i.isLt
    have := j.isLt
    split_ifs with h
    · simp only [Option.some.injEq, Fin.ext_iff]
      omega
    · simp only [false_iff, Option.some.injEq, Fin.ext_iff]
      omega

private def prefixBinding : Mapping 17 18 where
  toFun i := some i.castSucc
  invFun j := if h : j.val < 17 then some ⟨j.val, h⟩ else none
  inv i j := by
    have := i.isLt
    have := j.isLt
    split_ifs with h
    · simp only [Option.some.injEq, Fin.ext_iff, Fin.val_castSucc, eq_comm]
    · simp only [false_iff, Option.some.injEq, Fin.ext_iff, Fin.val_castSucc]
      omega

-- Filling the first literal hole before SWAP16 freezes the wrong output.
private def literalSource : Stack := List.replicate 16 zero ++ [one]
private def literalTarget : Stack := [one] ++ List.replicate 16 zero ++ [one]
private def literalState : State literalSource literalTarget ∅ where
  planned_mapping := by simpa [literalSource, literalTarget] using shiftedMapping 17 1
  stack := literalSource
  trace := .Lit literalSource
  mapping := by simpa [literalSource, literalTarget] using shiftedMapping 17 1
  pending_generations := 1

example : literalState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, literalState.mapping i = some j → literalState.stack[i] = literalTarget[j] := by decide
example : literalState.missingValues = [one] := by decide
#guard decide ((runIfValid literalState).map (fun result => result.1) =
    .error (.blocked 1))
#guard decide (checkedBuild ∅ literalSource literalTarget {one} = true)
#guard decide (checkedAdapter literalState literalTarget = true)

-- SWAP16 can recover a nonfree source that the initial DUP scan rejects.
private def seedSource : Stack := [a] ++ List.replicate 16 zero
private def seedTarget : Stack := List.replicate 16 zero ++ [a, a]
private def seedBinding : Mapping 17 18 := prefixBinding.swapDestinations 0 16
private def seedState : State seedSource seedTarget ∅ where
  planned_mapping := by simpa [seedSource, seedTarget] using seedBinding
  stack := seedSource
  trace := .Lit seedSource
  mapping := by simpa [seedSource, seedTarget] using seedBinding
  pending_generations := 1

example : seedState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, seedState.mapping i = some j → seedState.stack[i] = seedTarget[j] := by decide
example : seedState.missingValues = [a] := by decide
#guard decide ((runIfValid seedState).map (fun result => result.1) =
    .error (.blocked 1))
#guard decide (checkedBuild ∅ seedSource seedTarget {a} = true)
#guard decide (checkedAdapter seedState seedTarget = true)

-- A source already at depth15 becomes unreachable after the wrong addition.
private def hiddenSource : Stack := [zero, a] ++ List.replicate 15 zero
private def hiddenTarget : Stack := [zero, a, zero, a] ++ List.replicate 15 zero
private def hiddenState : State hiddenSource hiddenTarget ∅ where
  planned_mapping := by simpa [hiddenSource, hiddenTarget] using shiftedMapping 17 2
  stack := hiddenSource
  trace := .Lit hiddenSource
  mapping := by simpa [hiddenSource, hiddenTarget] using shiftedMapping 17 2
  pending_generations := 2

example : hiddenState.Valid := ⟨by decide, by decide, by decide⟩
example : ∀ i j, hiddenState.mapping i = some j → hiddenState.stack[i] = hiddenTarget[j] := by decide
example : hiddenState.missingValues = [zero, a] := by decide
example : Shuffler.Generate.Ready ∅ hiddenSource [zero, a] := by decide
#guard decide ((runIfValid hiddenState).map (fun result => result.1) =
    .error (.blocked 1))
#guard decide (checkedBuild ∅ hiddenSource hiddenTarget ({zero} + {a}) = true)
#guard decide (checkedAdapter hiddenState hiddenTarget = true)

-- Equal values permit a new occurrence assignment without moving a deep slot.
private def equalSource : Stack := List.replicate 18 zero
private def equalBinding : Mapping 18 18 := (Equiv.swap 0 17).toPEquiv
private def equalState : State equalSource equalSource ∅ where
  planned_mapping := by simpa [equalSource] using equalBinding
  stack := equalSource
  trace := .Lit equalSource
  mapping := by simpa [equalSource] using equalBinding
  pending_generations := 0

example : equalState.Valid := ⟨by decide, by decide, by decide⟩
#guard decide ((runIfValid equalState).map (fun result => result.1) =
    .error (.blocked 1))
#guard decide (checkedBuild ∅ equalSource equalSource 0 = true)
#guard decide (checkedAdapter equalState equalSource = true)

-- Empty and one-operation cases execute the production constructors.
#guard decide ((build ∅ [] [] 0).map (fun built => operations built.trace) = some [])
#guard decide ((build ∅ [] [zero] {zero}).map (fun built => operations built.trace) =
    some [.push zero])
#guard decide ((build {⟨42⟩} [] [a] {a}).map (fun built => operations built.trace) =
    some [.load ⟨42⟩])
#guard decide (checkedBuild ∅ [a] [a, a] {a} = true)

-- With no growth, the planner still moves unequal values into target order.
#guard decide (checkedBuild ∅ [a, b, zero] [zero, a, b] 0 = true)

-- The current instruction model permits DUP of a function return label.
#guard decide (checkedBuild ∅ [.FunctionReturnLabel]
    [.FunctionReturnLabel, .FunctionReturnLabel] {.FunctionReturnLabel} = true)

-- Repeated demand and both sides of the 16/17-slot boundary.
#guard decide (checkedBuild ∅ [a] (List.replicate 41 a) (List.replicate 40 a : Multiset Value) =
    true)
#guard decide (checkedBuild ∅ (List.replicate 16 a) (List.replicate 17 a) {a} = true)
#guard decide (checkedBuild ∅ (List.replicate 17 a) (List.replicate 18 a) {a} = true)
#guard decide (checkedBuild ∅ ([zero] ++ List.replicate 17 a) ([zero] ++ List.replicate 18 a) {a} =
    true)

-- Failed count, source, prefix, and combined output/seed conditions reject.
#guard decide ((build ∅ [a] [] 0).isNone = true)
#guard decide ((build ∅ [a] [a, a, a] {a}).isNone = true)
#guard decide ((build ∅ [] [a] {a}).isNone = true)
#guard decide ((build ∅ ([a] ++ List.replicate 17 zero)
    ([zero, a] ++ List.replicate 16 zero) 0).isNone = true)
#guard decide ((build ∅ (List.replicate 16 zero ++ [a])
    ([a] ++ List.replicate 16 zero ++ [a]) {a}).isNone = true)

-- The adapter starts from the current stack and retains the historical trace.
private def poppedState : State [zero, one] [zero, zero] ∅ where
  planned_mapping := ⊥
  stack := [zero]
  trace := .Pop (by decide) (.Lit [zero, one])
  mapping := (⊥ : Mapping 1 2).bind 0 0 rfl rfl
  pending_generations := 1

example : poppedState.Valid := ⟨by decide, by decide, by decide⟩
#guard decide (checkedAdapter poppedState [zero, zero] = true)
#guard decide ((buildComplete poppedState).map (fun result => (operations result.2).head?) =
    some (some .pop))

-- The adapter targets the mapping's concrete expectedStack at wildcard slots.
private def wildcardState : State [a] [.Wildcard] ∅ where
  planned_mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  stack := [a]
  trace := .Lit [a]
  mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  pending_generations := 0

example : wildcardState.Valid := ⟨by decide, by decide, by decide⟩
#guard decide (checkedAdapter wildcardState [a] = true)

-- A different wildcard assignment can be feasible when this expectedStack is not.
private def patternSource : Stack := [a, b] ++ List.replicate 16 zero
private def pattern : Stack := [.Wildcard, .Wildcard] ++ List.replicate 16 zero
private def patternBinding : Mapping 18 18 := (Equiv.swap 0 1).toPEquiv
private def patternState : State patternSource pattern ∅ where
  planned_mapping := by simpa [patternSource, pattern] using patternBinding
  stack := patternSource
  trace := .Lit patternSource
  mapping := by simpa [patternSource, pattern] using patternBinding
  pending_generations := 0

example : patternState.Valid := ⟨by decide, by decide, by decide⟩
example : StackMatches patternSource pattern := by decide
#guard decide ((buildComplete patternState).isNone = true)

end BuildBottomUpCompleteTests
