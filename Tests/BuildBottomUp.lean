import Shuffler.BuildBottomUp.Theorems

namespace BuildBottomUpTests

-- Attaching a proof keeps both success values and errors unchanged.
example (result : Except ShuffleErr ℕ) : result.attach.map Subtype.val = result := by
  cases result <;> rfl

-- The C++ helpers leave the counter unchanged; produce updates it.
example (state : State source target spills) (slot : Value) (dest : Fin target.length)
    (hgen : slot.can_be_freely_generated ∨ spills.is_spilled slot)
    (hdest : state.mapping.symm dest = none) :
    (state.push slot dest hgen hdest).pending_generations = state.pending_generations := rfl

example (state : State source target spills) (copy : Fin state.stack.length)
    (dest : Fin target.length) (hdup : state.stack.is_dup_reachable copy)
    (hdest : state.mapping.symm dest = none) :
    (state.dup copy dest hdup hdest).pending_generations = state.pending_generations := rfl

-- Pushing a spilled variable records a load and keeps the previous trace.
example (state : State source target spills) (id : VarId) (dest : Fin target.length)
    (hspilled : id ∈ spills) (hdest : state.mapping.symm dest = none) :
    (state.push (.Var id) dest (Or.inr hspilled) hdest).trace =
      Trace.Load id hspilled state.trace := rfl

-- Literals and wildcards still record pushes.
example (state : State source target spills) (word : Word) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) :
    (state.push (.Lit word) dest (by simp [Value.can_be_freely_generated]) hdest).trace =
      Trace.Push (.Lit word) (by simp [Value.can_be_freely_generated]) state.trace := rfl

example (state : State source target spills) (dest : Fin target.length)
    (hdest : state.mapping.symm dest = none) :
    (state.push .Wildcard dest (by simp [Value.can_be_freely_generated]) hdest).trace =
      Trace.Push .Wildcard (by decide) state.trace := rfl

def emptyState (target : Stack) (spills : SpillSet) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

def spilled : State [] [.Var ⟨37⟩] {⟨37⟩} := emptyState _ _

-- Produce loads a spilled variable even when the stack has no copy.
example : spilled.produce 0 rfl (by unfold State.is_available; decide) =
    .ok { spilled.push (.Var ⟨37⟩) 0 (by decide) rfl with pending_generations := 0 } := rfl

-- Loading fills the last unbound target position; produce updates the counter.
example : (spilled.push (.Var ⟨37⟩) 0 (by decide) rfl).pending_generations = 1 := rfl
example : ((spilled.push (.Var ⟨37⟩) 0 (by decide) rfl).mapping.symm 0).map Fin.val =
    some 0 := rfl

-- Produce can also push a literal when no copy exists.
example : (emptyState [.Lit 0] ∅).produce 0 rfl (by unfold State.is_available; decide) =
    .ok { (emptyState [.Lit 0] ∅).push (.Lit 0) 0 (by decide) rfl with pending_generations := 0 } := rfl

example : (emptyState [.Wildcard] ∅).produce 0 rfl (by unfold State.is_available; decide) =
    .ok { (emptyState [.Wildcard] ∅).push .Wildcard 0 (by decide) rfl with pending_generations := 0 } := rfl

def copyState (depth : ℕ) (spills : SpillSet) :
    State (.Var ⟨37⟩ :: List.replicate depth (.Lit 0)) [.Var ⟨37⟩] spills where
  planned_mapping := ⊥
  stack := .Var ⟨37⟩ :: List.replicate depth (.Lit 0)
  trace := .Lit _
  mapping := ⊥
  pending_generations := 1

-- The deepest reachable copy is duplicated, even if it is also spilled.
example : (copyState MAX_DUP_DEPTH {⟨37⟩}).produce 0 rfl (by unfold State.is_available; decide) =
    .ok { (copyState MAX_DUP_DEPTH {⟨37⟩}).dup ⟨0, by decide⟩ 0 (by decide) rfl with
      pending_generations := 0 } := rfl

-- One slot beyond DUP reach blocks unless a spill can be loaded.
example : (copyState (MAX_DUP_DEPTH + 1) ∅).produce 0 rfl
    (by unfold State.is_available; decide) = .error (.Blocked 1) := rfl
example : (copyState (MAX_DUP_DEPTH + 1) {⟨37⟩}).produce 0 rfl
    (by unfold State.is_available; decide) =
    .ok { (copyState (MAX_DUP_DEPTH + 1) {⟨37⟩}).push (.Var ⟨37⟩) 0 (by decide) rfl with
      pending_generations := 0 } := rfl

-- Neither an empty spill set nor a different spilled ID permits a load.
#check_failure ((emptyState [.Var ⟨37⟩] ∅).push (.Var ⟨37⟩) 0 (by decide) rfl)
#check_failure (spilled.push (.Var ⟨38⟩) 0 (by decide) rfl)

-- Produce requires a copy, a spill, or a value that can be freely generated.
#check_failure ((emptyState [.Var ⟨37⟩] ∅).produce 0 rfl (by unfold State.is_available; decide))
#check_failure ((emptyState [.Var ⟨37⟩] {⟨38⟩}).produce 0 rfl (by unfold State.is_available; decide))

/-- info: 'State.produce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.produce

/-- info: 'State.produce_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.produce_top

/-- info: 'State.produce_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.produce_pending

-- A bound destination cannot be filled again.
#check_failure ((spilled.push (.Var ⟨37⟩) 0 (by decide) rfl).push
  (.Var ⟨37⟩) 0 (by decide) (by decide))

end BuildBottomUpTests
