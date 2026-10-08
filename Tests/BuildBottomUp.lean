import Tests.BuildBottomUpObservations

open Shuffler.BuildBottomUp BuildBottomUpTestSupport

namespace BuildBottomUpTests

-- The C++ helpers leave the counter unchanged; produce updates it.
example (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hdest : state.mapping.symm dest = none) :
    (state.push slot dest).map (·.pending_generations) = .ok state.pending_generations := by
  cases slot <;> simp [State.push, State.positionOf, requires, hdest, hgen] <;> rfl

example (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.isDupReachable copy)
    (hdest : state.mapping.symm dest = none) :
    (state.dup copy.val dest).map (·.pending_generations) = .ok state.pending_generations := by
  simp [State.dup, State.positionOf, index, copy.isLt, requires, hdest, hdup]
  rfl

-- Pushing a spilled variable records a load and keeps the previous trace.
example (state : State source target spills) (id : VarId) (dest : Fin target.length)
    (hspilled : id ∈ spills) (hdest : state.mapping.symm dest = none) :
    (state.push (.Var id) dest).map
      (fun next => (⟨next.stack, next.trace⟩ : (res : Stack) × Trace spills source res)) =
      .ok ⟨state.stack ++ [.Var id], Trace.Load id hspilled state.trace⟩ := by
  simp [State.push, State.positionOf, requires, hdest, SpillSet.is_spilled, hspilled]
  rfl

-- Literals and wildcards record pushes.
example (state : State source target spills) (word : Word) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) :
    (state.push (.Lit word) dest).map
      (fun next => (⟨next.stack, next.trace⟩ : (res : Stack) × Trace spills source res)) =
      .ok ⟨state.stack ++ [.Lit word], Trace.Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace⟩ := by
  simp [State.push, State.positionOf, requires, hdest, Value.can_be_freely_generated]
  rfl

example (state : State source target spills) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) :
    (state.push .Wildcard dest).map
      (fun next => (⟨next.stack, next.trace⟩ : (res : Stack) × Trace spills source res)) =
      .ok ⟨state.stack ++ [.Wildcard], Trace.Push .Wildcard (by decide) state.trace⟩ := by
  simp [State.push, State.positionOf, requires, hdest, Value.can_be_freely_generated]
  rfl

private def emptyState (target : Stack) (spills : SpillSet) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

private def spilled : State [] [.Var ⟨37⟩] {⟨37⟩} := emptyState _ _

private def observeState (result : Except Error (State source target spills)) :=
  result.map fun state =>
    (state.stack, operations state.trace,
      List.ofFn (fun dest => (state.mapping.symm dest).map Fin.val), state.pending_generations)

-- Produce loads a spilled variable and fills the last unbound target position.
example : observeState (spilled.produce 0) =
    .ok ([.Var ⟨37⟩], [.load ⟨37⟩], [some 0], 0) := rfl

-- Push fills the binding but leaves the counter for produce to update.
example : observeState (spilled.push (.Var ⟨37⟩) 0) =
    .ok ([.Var ⟨37⟩], [.load ⟨37⟩], [some 0], 1) := rfl

example : observeState ((emptyState [.Lit 0] ∅).produce 0) =
    .ok ([.Lit 0], [.push (.Lit 0)], [some 0], 0) := rfl
example : observeState ((emptyState [.Wildcard] ∅).produce 0) =
    .ok ([.Wildcard], [.push .Wildcard], [some 0], 0) := rfl

private def copyState (depth : ℕ) (spills : SpillSet) :
    State (.Var ⟨37⟩ :: List.replicate depth (.Lit 0)) [.Var ⟨37⟩] spills where
  planned_mapping := ⊥
  stack := .Var ⟨37⟩ :: List.replicate depth (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := 1

-- The deepest reachable copy is duplicated, even if it is also spilled.
example : observeState ((copyState MAX_DUP_DEPTH {⟨37⟩}).produce 0) =
    .ok ((copyState MAX_DUP_DEPTH {⟨37⟩}).stack ++ [.Var ⟨37⟩], [.dup 16], [some 16], 0) := rfl

-- One slot beyond DUP reach blocks unless a spill can be loaded.
example : (copyState (MAX_DUP_DEPTH + 1) ∅).produce 0 = .error (.blocked 1) := rfl
example : observeState ((copyState (MAX_DUP_DEPTH + 1) {⟨37⟩}).produce 0) =
    .ok ((copyState (MAX_DUP_DEPTH + 1) {⟨37⟩}).stack ++ [.Var ⟨37⟩], [.load ⟨37⟩], [some 17], 0) := rfl

-- Neither an empty spill set nor a different spilled ID permits a load.
example : (emptyState [.Var ⟨37⟩] ∅).push (.Var ⟨37⟩) 0 =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl
example : spilled.push (.Var ⟨38⟩) 0 =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl

-- Produce requires a copy, a spill, or a value that can be freely generated.
example : (emptyState [.Var ⟨37⟩] ∅).produce 0 =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl
example : (emptyState [.Var ⟨37⟩] {⟨38⟩}).produce 0 =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl

/-- info: 'Shuffler.BuildBottomUp.State.produce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.produce

-- A bound destination cannot be filled again.
example : ((·.push (.Var ⟨37⟩) 0) >=> (·.push (.Var ⟨37⟩) 0)) spilled =
    .error (.assertion "destination already bound to a slot") := rfl

end BuildBottomUpTests
