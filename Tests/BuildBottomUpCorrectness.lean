import Shuffler

open Shuffler.BuildBottomUp

set_option maxRecDepth 16384

-- The public results apply to the production function.
example (initial : State source target spills) (hvalid : initial.Valid)
    (hsmall : initial.stack.length < MAX_DUP_DEPTH)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target,
      buildBottomUp initial = .ok ⟨target, trace⟩ :=
  buildBottomUp_correct_small initial hvalid hsmall hmapped

example (initial : State source target spills) (hvalid : initial.Valid)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j])
    (trace : Trace spills source result)
    (hrun : buildBottomUp initial = .ok ⟨result, trace⟩) : result = target :=
  buildBottomUp_correct_of_ok initial hvalid hmapped hrun

-- The success bound includes DUP16 and places no limit on the target length.
example (initial : State source target spills) (hvalid : initial.Valid)
    (hsmall : initial.stack.length ≤ MAX_DUP_DEPTH + 1)
    (hmapped : ∀ i j, initial.mapping i = some j → initial.stack[i] = target[j]) :
    ∃ trace : Trace spills source target,
      buildBottomUp initial = .ok ⟨target, trace⟩ :=
  buildBottomUp_correct_within_dup_reach initial hvalid hsmall hmapped

namespace BuildBottomUpCorrectnessTests

private def emptyState : State [] [] ∅ where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := 0

example : ∃ trace : Trace ∅ [] [], buildBottomUp emptyState = .ok ⟨[], trace⟩ := by
  apply buildBottomUp_correct_small emptyState
  · exact ⟨rfl, by decide, by decide⟩
  · decide
  · intro i; exact Fin.elim0 i

example : (buildBottomUp emptyState).map (fun result => result.1) = .ok [] := by native_decide

private def retained (n extra : ℕ) : Mapping n (n + extra) where
  toFun := fun i => some ⟨i.val, by omega⟩
  invFun := fun j => if h : j.val < n then some ⟨j.val, h⟩ else none
  inv a b := by
    have := a.isLt
    split_ifs with h <;> simp_all [Fin.ext_iff, eq_comm]
    omega

private def copyState (padding extra : ℕ) : State
    (.Var ⟨37⟩ :: List.replicate padding (.Lit 0))
    ((.Var ⟨37⟩ :: List.replicate padding (.Lit 0)) ++
      List.replicate extra (.Lit 0) ++ [.Var ⟨37⟩]) ∅ where
  planned_mapping := ⊥
  stack := .Var ⟨37⟩ :: List.replicate padding (.Lit 0)
  trace := .Lit _
  mapping := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using retained (padding + 1) (extra + 1)
  pending_generations := extra + 1

-- The copy must be duplicated before later pushes put it beyond DUP reach.
example : (buildBottomUp (copyState 0 40)).map (fun result => result.1) =
    .ok ([.Var ⟨37⟩] ++ List.replicate 40 (.Lit 0) ++ [.Var ⟨37⟩]) := by native_decide

example : ∃ trace : Trace ∅ [.Var ⟨37⟩]
      ([.Var ⟨37⟩] ++ List.replicate 40 (.Lit 0) ++ [.Var ⟨37⟩]),
    buildBottomUp (copyState 0 40) = .ok ⟨_, trace⟩ := by
  apply buildBottomUp_correct_small (copyState 0 40)
  · exact ⟨by decide, by decide, by decide⟩
  · decide
  · decide

-- Sixteen initial slots succeed. A seventeenth can make the needed copy unreachable.
example : (buildBottomUp (copyState 15 0)).map (fun result => result.1) =
    .ok ((.Var ⟨37⟩ :: List.replicate 15 (.Lit 0)) ++ [.Var ⟨37⟩]) := by native_decide

example : (copyState 16 0).Valid := ⟨by decide, by decide, by decide⟩

example : ∀ i j, (copyState 16 0).mapping i = some j →
    (copyState 16 0).stack[i] =
      ((.Var ⟨37⟩ :: List.replicate 16 (.Lit 0)) ++ [.Var ⟨37⟩])[j] := by decide

example : (buildBottomUp (copyState 16 0)).map (fun result => result.1) =
    .error (.blocked 1) := by native_decide

-- Validity and the size bound do not imply that the mapping respects target values.
private def mismatched : State [.Lit 1] [.Lit 2] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 1]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 1).bind 0 0 rfl rfl
  pending_generations := 0

example : mismatched.Valid := ⟨by decide, by decide, by decide⟩
example : mismatched.stack.length < MAX_DUP_DEPTH := by decide
example : ¬(∀ i j, mismatched.mapping i = some j → mismatched.stack[i] = ([.Lit 2] : Stack)[j]) := by
  decide
example : (buildBottomUp mismatched).map (fun result => result.1) = .ok [.Lit 1] := by native_decide

end BuildBottomUpCorrectnessTests
