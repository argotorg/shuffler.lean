module

public meta import Shuffler.Emission.Defs
import Shuffler.Emission.Defs

open Shuffler.Emission

namespace DupTests

private def initial (stack : Stack) : State stack [.Wildcard] ∅ where
  planned_mapping := ⊥
  stack := stack
  trace := .Lit stack
  mapping := ⊥
  pending_generations := 1

private def duplicates (stack : Stack) (offset : ℕ) (value : Value) : Bool :=
  match (initial stack).dup offset 0 with
  | .error _ => false
  | .ok state => decide (state.stack = stack ++ [value]) &&
      decide ((state.mapping.symm 0).map Fin.val = some stack.length)

-- A function return label cannot be duplicated, including at the depth limit.
#guard match (initial [.FunctionReturnLabel]).dup 0 0 with
  | .error (.assertion "Cannot dup function return label") => true
  | _ => false
#guard match (initial (.FunctionReturnLabel :: List.replicate 15 (.Lit 0))).dup 0 0 with
  | .error (.assertion "Cannot dup function return label") => true
  | _ => false

-- C++ checks reach before it checks the slot kind.
#guard match (initial (.FunctionReturnLabel :: List.replicate 16 (.Lit 0))).dup 0 0 with
  | .error (.assertion "Stack too deep") => true
  | _ => false

-- Variables, literals, and junk can be duplicated.
#guard duplicates [.Var ⟨0⟩] 0 (.Var ⟨0⟩)
#guard duplicates [.Lit 7] 0 (.Lit 7)
#guard duplicates [.Wildcard] 0 .Wildcard
#guard duplicates [.FunctionReturnLabel, .Var ⟨0⟩] 1 (.Var ⟨0⟩)
#guard duplicates (.Var ⟨0⟩ :: List.replicate 15 (.Lit 0)) 0 (.Var ⟨0⟩)

end DupTests
