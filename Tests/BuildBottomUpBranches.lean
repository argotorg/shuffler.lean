import Shuffler.BuildBottomUp.Defs

open Shuffler.BuildBottomUp

set_option maxRecDepth 16384

namespace BuildBottomUpBranchTests

-- The new top is the only unbound target. Generating it must revisit offset zero.
private def newTopState : State [.Lit 10, .Lit 20] [.Lit 20, .Lit 10, .Lit 7] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20]
  trace := .Lit _
  mapping := ((⊥ : Mapping 2 3).bind 0 1 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

example :
    (buildBottomUp newTopState).toOption.map
        (fun result => result.1) = some [.Lit 20, .Lit 10, .Lit 7] := by
  native_decide

-- Keep the first seventeen destinations and leave the eighteenth unbound.
private def retained : Mapping 17 18 where
  toFun := fun i => some i.castSucc
  invFun := fun j => if h : j.val < 17 then some ⟨j.val, h⟩ else none
  inv a b := by
    have := a.isLt
    split_ifs with h <;> simp_all [Fin.ext_iff, Fin.val_castSucc, eq_comm]
    omega

private abbrev urgentSource : Stack :=
  [.Lit 0, .Var ⟨37⟩] ++ List.replicate 15 (.Lit 0)

private abbrev urgentTarget : Stack := urgentSource ++ [.Var ⟨37⟩]

-- At offset two, the copy at offset one is at the last reachable DUP depth.
-- The urgent destination is seventeen; destination two is already bound.
private def urgentState : State urgentSource urgentTarget ∅ where
  planned_mapping := ⊥
  stack := urgentSource
  trace := .Lit _
  mapping := retained.swapDestinations 2 3
  pending_generations := 1

-- The loop skips the first two destinations before it reaches the urgent copy.
example : (List.ofFn fun i => decide (urgentState.isFinal i)).take 3 = [true, true, false] := by
  decide

example :
    (buildBottomUp urgentState).toOption.map
        (fun result => result.1) = some urgentTarget := by
  native_decide

private def missingCopyState : State [.Lit 10, .Lit 20] [.Lit 20, .Lit 10, .Var ⟨37⟩] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20]
  trace := .Lit _
  mapping := ((⊥ : Mapping 2 3).bind 0 1 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

-- An unavailable target value returns an assertion error.
example : (buildBottomUp missingCopyState).map (fun result => result.1) =
    .error (.assertion "generated slot has no copy on the stack and is not spilled") := by
  native_decide

private def surplusState : State [.Lit 10, .Lit 20, .Lit 7] [.Lit 20, .Lit 10, .Lit 7] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20, .Lit 7]
  trace := .Lit _
  mapping := ((⊥ : Mapping 3 3).bind 0 1 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

-- A surplus generation returns the size assertion.
example : (buildBottomUp surplusState).map (fun result => result.1) =
    .error (.assertion "stack and target sizes differ") := by
  native_decide

end BuildBottomUpBranchTests
