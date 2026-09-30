import Shuffler.BuildBottomUp.HelperProofs
import Tests.BuildBottomUpObservations

open Shuffler.BuildBottomUp BuildBottomUpTestSupport

namespace BuildBottomUpTests

-- The C++ helpers leave the counter unchanged; produce updates it.
example (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hdest : state.mapping.symm dest = none) :
    ((push slot dest).exec state).map (·.pending_generations) = .ok state.pending_generations := by
  cases slot <;> simp [push, Action.exec, requires, hdest, hgen] <;> rfl

example (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.isDupReachable copy)
    (hdest : state.mapping.symm dest = none) :
    ((dup copy.val dest).exec state).map (·.pending_generations) = .ok state.pending_generations := by
  simp [dup, Action.exec, index, copy.isLt, requires, hdest, hdup]
  rfl

-- Pushing a spilled variable records a load and keeps the previous trace.
example (state : State source target spills) (id : VarId) (dest : Fin target.length)
    (hspilled : id ∈ spills) (hdest : state.mapping.symm dest = none) :
    ((push (.Var id) dest).exec state).map (fun next => (⟨next.stack, next.trace⟩ : Result source spills)) =
      .ok ⟨state.stack ++ [.Var id], Trace.Load id hspilled state.trace⟩ := by
  simp [push, Action.exec, requires, hdest, SpillSet.is_spilled, hspilled]
  rfl

-- Literals and wildcards record pushes.
example (state : State source target spills) (word : Word) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) :
    ((push (.Lit word) dest).exec state).map (fun next => (⟨next.stack, next.trace⟩ : Result source spills)) =
      .ok ⟨state.stack ++ [.Lit word], Trace.Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace⟩ := by
  simp [push, Action.exec, requires, hdest, Value.can_be_freely_generated]
  rfl

example (state : State source target spills) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) :
    ((push .Wildcard dest).exec state).map (fun next => (⟨next.stack, next.trace⟩ : Result source spills)) =
      .ok ⟨state.stack ++ [.Wildcard], Trace.Push .Wildcard (by decide) state.trace⟩ := by
  simp [push, Action.exec, requires, hdest, Value.can_be_freely_generated]
  rfl

private def emptyState (target : Stack) (spills : SpillSet) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

private def spilled : State [] [.Var ⟨37⟩] {⟨37⟩} := emptyState _ _

private def observeState (result : M (State source target spills)) :=
  result.map fun state =>
    (state.stack, operations state.trace,
      List.ofFn (fun dest => (state.mapping.symm dest).map Fin.val), state.pending_generations)

-- Produce loads a spilled variable and fills the last unbound target position.
example : observeState ((produce 0).exec spilled) =
    .ok ([.Var ⟨37⟩], [.load ⟨37⟩], [some 0], 0) := rfl

-- Push fills the binding but leaves the counter for produce to update.
example : observeState ((push (.Var ⟨37⟩) 0).exec spilled) =
    .ok ([.Var ⟨37⟩], [.load ⟨37⟩], [some 0], 1) := rfl

example : observeState ((produce 0).exec (emptyState [.Lit 0] ∅)) =
    .ok ([.Lit 0], [.push (.Lit 0)], [some 0], 0) := rfl
example : observeState ((produce 0).exec (emptyState [.Wildcard] ∅)) =
    .ok ([.Wildcard], [.push .Wildcard], [some 0], 0) := rfl

private def copyState (depth : ℕ) (spills : SpillSet) :
    State (.Var ⟨37⟩ :: List.replicate depth (.Lit 0)) [.Var ⟨37⟩] spills where
  planned_mapping := ⊥
  stack := .Var ⟨37⟩ :: List.replicate depth (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := 1

-- The deepest reachable copy is duplicated, even if it is also spilled.
example : observeState ((produce 0).exec (copyState MAX_DUP_DEPTH {⟨37⟩})) =
    .ok ((copyState MAX_DUP_DEPTH {⟨37⟩}).stack ++ [.Var ⟨37⟩], [.dup 16], [some 16], 0) := rfl

-- One slot beyond DUP reach blocks unless a spill can be loaded.
example : (produce 0).exec (copyState (MAX_DUP_DEPTH + 1) ∅) = .error (.blocked 1) := rfl
example : observeState ((produce 0).exec (copyState (MAX_DUP_DEPTH + 1) {⟨37⟩})) =
    .ok ((copyState (MAX_DUP_DEPTH + 1) {⟨37⟩}).stack ++ [.Var ⟨37⟩], [.load ⟨37⟩], [some 17], 0) := rfl

-- Neither an empty spill set nor a different spilled ID permits a load.
example : (push (.Var ⟨37⟩) 0).exec (emptyState [.Var ⟨37⟩] ∅) =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl
example : (push (.Var ⟨38⟩) 0).exec spilled =
    .error (.assertion "pushed slot cannot be generated or loaded") := rfl

-- Produce requires a copy, a spill, or a value that can be freely generated.
example : (produce 0).exec (emptyState [.Var ⟨37⟩] ∅) =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl
example : (produce 0).exec (emptyState [.Var ⟨37⟩] {⟨38⟩}) =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := rfl

-- The helper contract proves the top binding and counter consistency for every success.
example (state : State source target spills) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) (ha : state.isAvailable dest) :
    Spec ((produce dest).exec state) (fun next =>
      0 < next.stack.length ∧ positionOf next dest.val = some (next.stack.length - 1)) := by
  apply (Spec.of_action (produce_spec state dest hdest ha)).mono
  intro next h
  exact ⟨by have := h.size; omega, h.top⟩

example (state : State source target spills) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) (ha : state.isAvailable dest)
    (hp : state.mapping.unmapped_target_slots = state.pending_generations) :
    Spec ((produce dest).exec state) (fun next =>
      next.mapping.unmapped_target_slots = next.pending_generations) := by
  apply (Spec.of_action (produce_spec state dest hdest ha)).mono
  intro next h
  have := h.count
  have := h.pending_eq
  omega

/-- info: 'Shuffler.BuildBottomUp.produce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms produce

/-- info: 'Shuffler.BuildBottomUp.produce_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms produce_spec

-- A bound destination cannot be filled again.
example : (do
    push (.Var ⟨37⟩) 0
    push (.Var ⟨37⟩) 0).exec spilled =
    .error (.assertion "destination already bound to a slot") := rfl

end BuildBottomUpTests
