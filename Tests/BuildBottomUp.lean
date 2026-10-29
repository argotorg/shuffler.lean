import Shuffler.BuildBottomUp.Lemmas.StaticDecision

open Shuffler.Emission

set_option maxRecDepth 16384

namespace BuildBottomUpTests

private instance (state : State source target spills) : Decidable state.Valid :=
  decidable_of_iff
    (state.stack.length + state.pending_generations = target.length ∧
      state.mapping.unmapped_target_slots = state.pending_generations ∧
      (∀ j, state.isAvailable j) ∧
      ∀ j, target[j].isFunctionReturnLabel → (state.mapping.symm j).isSome)
    ⟨fun ⟨hs, hp, ha, hl⟩ => ⟨hs, hp, ha, hl⟩,
      fun h => ⟨h.size, h.pending, h.available, h.labels_bound⟩⟩

-- Every injection from source positions to target positions.
private def mappings (m n : ℕ) : List (Mapping m n) :=
  (List.finRange m).foldl (fun maps src => maps.flatMap fun mapping =>
    (List.finRange n).filterMap fun dest =>
      if hs : mapping src = none then
        if hd : mapping.symm dest = none then some (mapping.bind src dest hs hd)
        else none
      else none) [⊥]

-- Binds source position i to destinations[i]. Out of range or taken destinations are skipped.
private def mappingByDest (n m : ℕ) (destinations : List ℕ) : Mapping n m :=
  (List.finRange n).foldl (fun mapping i =>
    match destinations[i.val]? with
    | some j =>
      if hj : j < m then
        if hi : mapping i = none then
          if hu : mapping.symm ⟨j, hj⟩ = none then mapping.bind i ⟨j, hj⟩ hi hu
          else mapping
        else mapping
      else mapping
    | none => mapping) ⊥

private def initial (source target : Stack) (mapping : Mapping source.length target.length) :
    State source target ∅ where
  planned_mapping := mapping
  stack := source
  trace := .Lit source
  mapping := mapping
  pending_generations := target.length - source.length

-- Bound destinations retain their assigned values. Unbound destinations are generated.
-- The values and mappings are independent, so the expected stack need not equal target.
private def expectedStack (state : State source target spills) : Stack :=
  List.ofFn fun dest : Fin target.length =>
    match state.mapping.symm dest with
    | some pos => state.stack[pos]
    | none => target[dest]

-- These stacks fit within reach, so every valid state must produce the expected stack.
private def matchesExpected (state : State source target ∅) : Option Bool :=
  if h : state.Valid then
    some (match buildBottomUp state h with
      | .ok result => result.blocked.isNone && decide (result.state.stack = expectedStack state)
      | .error _ => false)
  else none

-- Every source of length below 4, every longer target of length below 5 over two values, and every
-- injection between them. Invalid states are skipped.
private def exhaustive : List Bool :=
  (List.range 4).flatMap fun m => ((List.range 5).drop m).flatMap fun n =>
    (List.replicate m [.Lit 0, .Lit 1]).sections.flatMap fun source =>
      (List.replicate n [.Lit 0, .Lit 1]).sections.flatMap fun target =>
        (mappings source.length target.length).filterMap fun mapping =>
          matchesExpected (initial source target mapping)

-- The count also checks that the validity filter does not skip every case.
example : (exhaustive.length, exhaustive.count false) = (4675, 0) := by native_decide

private def nextSeed (seed : ℕ) : ℕ := (seed * 1664525 + 1013904223) % 4294967296

private def shuffle (seed : ℕ) (xs : List α) : List α :=
  ((List.range xs.length).reverse.foldl (fun (seed, values) i =>
    let seed := nextSeed seed
    (seed, values.swap i (seed % (i + 1)))) (seed, xs)).2

private def sampleValue (seed : ℕ) : Value :=
  match seed % 8 with
  | 0 => .Var ⟨1⟩
  | 1 => .Var ⟨2⟩
  | 2 => .Lit 1
  | _ => .Lit 0

-- The StaticSuccess prediction and the buildBottomUp outcome for one pseudorandom valid state.
private def sample (n extra seed : ℕ) : Option (Bool × Bool) :=
  let source : Stack := (List.range n).map (fun i => sampleValue (nextSeed (seed + i)))
  let mapping := mappingByDest source.length (n + extra) (shuffle seed (List.range (n + extra)))
  let target : Stack := List.ofFn fun j : Fin (n + extra) =>
    match mapping.symm j with
    | some i => source[i]
    | none => sampleValue (nextSeed (seed + j.val))
  let state := initial source target (by simpa [target] using mapping)
  if h : state.Valid then
    some (decide (StaticSuccess state),
      match buildBottomUp state h with
      | .ok result => result.blocked.isNone
      | .error _ => false)
  else none

-- Report valid cases, successful runs, blocked runs, and disagreements between StaticSuccess and
-- buildBottomUp. Stack sizes cross the DUP and SWAP limits.
private def sampleReport : ℕ × ℕ × ℕ × ℕ :=
  let outcomes := [0, 1, 15, 16, 17, 18, 20, 28].flatMap fun n =>
    (List.range 8).flatMap fun extra => (List.range 12).filterMap (sample n extra)
  (outcomes.length, outcomes.countP (·.2), outcomes.countP (!·.2),
    outcomes.countP fun (predicted, actual) => predicted != actual)

example : sampleReport = (644, 414, 230, 0) := by native_decide

end BuildBottomUpTests
