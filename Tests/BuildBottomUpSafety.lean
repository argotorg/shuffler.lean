import Shuffler

open Shuffler.BuildBottomUp

-- The theorem applies to the production function and excludes each assertion reason.
example (initial : State source target spills) (h : initial.Valid) (reason : String) :
    buildBottomUp initial h ≠ .error (.assertion reason) :=
  buildBottomUp_no_assertion initial h reason

namespace BuildBottomUpSafetyTests

private def emptyState (target : Stack) (spills : SpillSet) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

-- This includes empty targets, literals, wildcards, and spilled variables.
private theorem emptyState_valid (target : Stack) (spills : SpillSet)
    (h : ∀ i : Fin target.length,
      target[i].can_be_freely_generated ∨ spills.is_spilled target[i]) :
    (emptyState target spills).Valid := by
  refine ⟨by simp [emptyState], by simp [emptyState], ?_⟩
  intro i
  rcases h i with hfree | hspill
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hspill)

example (target : Stack) (spills : SpillSet)
    (h : ∀ i : Fin target.length,
      target[i].can_be_freely_generated ∨ spills.is_spilled target[i]) (reason : String) :
    buildBottomUp (emptyState target spills) (emptyState_valid target spills h) ≠
      .error (.assertion reason) :=
  buildBottomUp_no_assertion _ _ reason

private def retainAll (n : ℕ) : Mapping n (n + 1) where
  toFun := fun i => some i.castSucc
  invFun := fun j => if h : j.val < n then some ⟨j.val, h⟩ else none
  inv a b := by
    have := a.isLt
    split_ifs with h <;> simp_all [Fin.ext_iff, Fin.val_castSucc, eq_comm]
    omega

private def deepCopy : State
    (.Var ⟨1⟩ :: List.replicate 16 (.Lit 0))
    ((.Var ⟨1⟩ :: List.replicate 16 (.Lit 0)) ++ [.Var ⟨1⟩]) ∅ where
  planned_mapping := retainAll 17
  stack := .Var ⟨1⟩ :: List.replicate 16 (.Lit 0)
  trace := .Lit _
  mapping := retainAll 17
  pending_generations := 1

-- Availability does not require a copy to be within DUP reach.
private theorem deepCopy_valid : deepCopy.Valid := by
  refine ⟨by decide, by decide, ?_⟩
  decide

example (reason : String) : buildBottomUp deepCopy deepCopy_valid ≠ .error (.assertion reason) :=
  buildBottomUp_no_assertion deepCopy deepCopy_valid reason

example : (buildBottomUp deepCopy deepCopy_valid).map (fun result => result.1) = .error (.blocked 1) := by
  native_decide

-- Each initial condition is needed: size, pending count, and availability.
private def surplus : State [.Lit 0] [] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 0]
  trace := .Lit _
  mapping := ⊥
  pending_generations := 0

example : ¬ surplus.Valid := by
  intro h
  have := h.size
  contradiction

-- Without the size condition the loop returns a stack longer than the target.
example : (buildBottomUp.loop 0 surplus).map (fun result => result.1.length) = .ok 1 := by
  native_decide

private def unbound : State [.Lit 0] [.Lit 0] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 0]
  trace := .Lit _
  mapping := ⊥
  pending_generations := 0

example : ¬ unbound.Valid := by
  intro h
  have := h.pending
  contradiction

example : (buildBottomUp.loop 0 unbound).map (fun result => result.1) =
    .error (.assertion "unmapped source slots") := by native_decide

example : ¬ (emptyState [.Var ⟨1⟩] ∅).Valid := by
  intro h
  have := h.available 0
  contradiction

example : (buildBottomUp.loop 0 (emptyState [.Var ⟨1⟩] ∅)).map (fun result => result.1) =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := by native_decide

-- Function return labels also need a copy, since they cannot be generated.
example : ¬ (emptyState [.FunctionReturnLabel] ∅).Valid := by
  intro h
  have := h.available 0
  contradiction

end BuildBottomUpSafetyTests
