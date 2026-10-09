import Shuffler.BuildBottomUp.Lemmas.StaticDecision

open Shuffler.BuildBottomUp

set_option maxRecDepth 16384

namespace BuildBottomUpStaticTests

private instance (state : State source target spills) : Decidable state.Valid :=
  decidable_of_iff
    (state.stack.length + state.pending_generations = target.length ∧
      state.mapping.unmapped_target_slots = state.pending_generations ∧
      ∀ j, state.isAvailable j)
    ⟨fun ⟨hs, hp, ha⟩ => ⟨hs, hp, ha⟩, fun h => ⟨h.size, h.pending, h.available⟩⟩

private def succeeds (state : State source target spills) (h : state.Valid) : Bool :=
  match buildBottomUp state h with
  | .ok _ => true
  | .error _ => false

private def mappingByDest (n m : Nat) (destinations : List Nat) : Mapping n m :=
  (List.finRange n).foldl (fun mapping i =>
    match destinations[i.val]? with
    | some j =>
      if hj : j < m then
        if hi : mapping i = none then
          if hu : mapping.symm ⟨j,hj⟩ = none then mapping.bind i ⟨j,hj⟩ hi hu
          else mapping
        else mapping
      else mapping
    | none => mapping) ⊥

private def stateFor (source target : Stack) (destinations : List Nat) (spills : SpillSet := ∅) :
    State source target spills where
  planned_mapping := mappingByDest source.length target.length destinations
  stack := source
  trace := .Lit source
  mapping := mappingByDest source.length target.length destinations
  pending_generations := target.length - source.length

private def checked (state : State source target spills) (expected : Bool) : Bool :=
  if h : state.Valid then decide (StaticSuccess state) == expected && succeeds state h == expected
  else false

private def emptyState : State [] [] ∅ where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := 0

private theorem emptyState_valid : emptyState.Valid := ⟨by decide, by decide, by decide⟩
example : decide (StaticSuccess emptyState) = true := by native_decide
example : (buildBottomUp emptyState emptyState_valid).map (fun result => result.1) = .ok [] := by
  native_decide

private def x : Value := .Var ⟨1⟩

-- A small initial stack can grow well beyond the DUP limit.
private def smallGrowing := stateFor [x] ([x] ++ List.replicate 40 (.Lit 0) ++ [x]) [0]
example : checked smallGrowing true := by native_decide

-- At width seventeen, an unequal placement removes one reachable copy of x.
private def boundarySource (copies : Nat) : Stack :=
  [.Lit 0] ++ List.replicate copies x ++ List.replicate (16 - copies) (.Lit 0)

private def boundaryTarget (copies : Nat) : Stack :=
  [x, .Lit 0] ++ List.replicate (copies - 1) x ++ List.replicate (16 - copies) (.Lit 0) ++ [x]

private def boundaryDestinations : List Nat := [1,0] ++ (List.range 15).map (· + 2)

private def boundaryState (copies : Nat) (spills : SpillSet := ∅) :=
  stateFor (boundarySource copies) (boundaryTarget copies) boundaryDestinations spills

example : checked (boundaryState 1) false := by native_decide
example : (buildBottomUp (boundaryState 1) (by native_decide)).map (fun result => result.1) =
    .error (.blocked 1) := by native_decide
example : checked (boundaryState 2) true := by native_decide
example : checked (boundaryState 1 {⟨1⟩}) true := by native_decide

-- The deep equal prefix ends at an unequal placement with two copies in reach.
private def equalPrefix := stateFor
  ([.Lit 0,x,.Lit 0,x] ++ List.replicate 14 (.Lit 0))
  ([.Lit 0,x,x,.Lit 0,.Lit 0,x] ++ List.replicate 14 (.Lit 0) ++ [x])
  ([0,2] ++ (List.range 16).map (· + 4))

example : checked equalPrefix true := by native_decide
example : (Success.cutoff equalPrefix, Success.copies equalPrefix 0 x,
    Success.copies equalPrefix 1 x, Success.copies equalPrefix 2 x) = (2,1,1,2) := by native_decide

-- Initial reachability can be lost after one generation at a deep equal position.
private def hiddenCopy := stateFor
  ([.Lit 0,x] ++ List.replicate 15 (.Lit 0))
  ([.Lit 0,x,.Lit 0,x] ++ List.replicate 15 (.Lit 0))
  ((List.range 17).map (· + 2))

example : checked hiddenCopy false := by native_decide
example : decide (Success.Ready hiddenCopy 0) = true ∧
    decide (Success.Ready hiddenCopy 1) = false := by native_decide

-- Equal values do not remove a deep nontrivial assignment cycle in Permute.
private def deepPermutation := stateFor (List.replicate 18 (.Lit 0))
  (List.replicate 18 (.Lit 0)) ([17] ++ (List.range 16).map (· + 1) ++ [0])

example : checked deepPermutation false := by native_decide
example : deepPermutation.pending_generations = 0 := by decide
example : (buildBottomUp deepPermutation (by native_decide)).map (fun result => result.1) =
    .error (.blocked 1) := by native_decide

private def deepIdentity := stateFor (List.replicate 24 (.Lit 0))
  (List.replicate 24 (.Lit 0)) (List.range 24)
example : checked deepIdentity true := by native_decide

-- Both runs finish generation before the seventeen-slot boundary. Only one
-- original cycle relation permits the remaining deep position to be fixed.
private def cycleAfterGeneration := stateFor (List.replicate 18 (.Lit 0))
  (List.replicate 19 (.Lit 0)) ((List.range 18).map (· + 1))
private def fixedAfterGeneration := stateFor (List.replicate 18 (.Lit 0))
  (List.replicate 19 (.Lit 0)) ([18] ++ (List.range 17).map (· + 1))

example : checked cycleAfterGeneration false := by native_decide
example : checked fixedAfterGeneration true := by native_decide

-- Success uses the assigned values. A wildcard target need not equal its result.
private def wildcard := stateFor [x] [.Wildcard] [0]
example : checked wildcard true := by native_decide
example : (buildBottomUp wildcard (by native_decide)).map (fun result => result.1) = .ok [x] := by
  native_decide

-- Validity alone also permits a value-incorrect concrete mapping.
private def mismatched := stateFor (List.replicate 20 (.Lit 0))
  (List.replicate 21 (.Lit 1)) (List.range 20)
example : checked mismatched true := by native_decide
example : (buildBottomUp mismatched (by native_decide)).map (fun result => result.1) =
    .ok (List.replicate 20 (.Lit 0) ++ [.Lit 1]) := by native_decide

-- The equivalence theorem has a validity assumption. This input lacks its target value.
private def unavailable := stateFor [x] [x, .Var ⟨2⟩] [0]
example : ¬unavailable.Valid := by native_decide
example : decide (StaticSuccess unavailable) = false := by native_decide

private def nextSeed (seed : Nat) : Nat := (seed * 1664525 + 1013904223) % 4294967296

private def shuffle (seed : Nat) (xs : List α) : List α :=
  ((List.range xs.length).reverse.foldl (fun (seed, values) i =>
    let seed := nextSeed seed
    (seed, values.swap i (seed % (i + 1)))) (seed, xs)).2

private def sampleValue (seed : Nat) : Value :=
  match seed % 8 with
  | 0 => .Var ⟨1⟩
  | 1 => .Var ⟨2⟩
  | 2 => .Lit 1
  | _ => .Lit 0

private def sample (n extra seed : Nat) : Option (Bool × Bool) :=
  let source : Stack := (List.range n).map (fun i => sampleValue (nextSeed (seed + i)))
  let mapping := mappingByDest source.length (n + extra) (shuffle seed (List.range (n + extra)))
  let target : Stack := List.ofFn fun j : Fin (n + extra) =>
    match mapping.symm j with
    | some i => source[i]
    | none => sampleValue (nextSeed (seed + j.val))
  let state : State source target ∅ := {
    planned_mapping := by simpa [target] using mapping
    stack := source
    trace := .Lit source
    mapping := by simpa [target] using mapping
    pending_generations := extra
  }
  if h : state.Valid then some (decide (StaticSuccess state), succeeds state h) else none

-- Report valid cases, successful runs, blocked runs, and disagreements. The
-- predicate is the production proposition through its executable instance.
private def sampleReport : Nat × Nat × Nat × Nat :=
  let outcomes := [0,1,15,16,17,18,20,28].flatMap fun n =>
    (List.range 8).flatMap fun extra => (List.range 12).filterMap (sample n extra)
  outcomes.foldl (fun (total, successes, errors, mismatches) (predicted, actual) =>
    (total + 1, successes + if actual then 1 else 0,
      errors + if actual then 0 else 1, mismatches + if predicted == actual then 0 else 1))
    (0,0,0,0)

example : sampleReport = (644,408,236,0) := by native_decide

end BuildBottomUpStaticTests
