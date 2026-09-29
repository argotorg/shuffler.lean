import Shuffler.BuildBottomUp.Defs

set_option maxRecDepth 16384

namespace BuildBottomUpCursorTests

private def emptyState (target : Stack) (spills : SpillSet := ∅) : State [] target spills where
  planned_mapping := ⊥
  stack := []
  trace := .Lit []
  mapping := ⊥
  pending_generations := target.length

-- The only target position must be processed before the loop returns.
example :
    (build_bottom_up 0 (emptyState [.Lit 7])
      (by intro i hi; omega) (by decide) (by decide)
      (by intro i; fin_cases i; unfold State.is_available; decide)).toOption.map
        (fun result => result.1) = some [.Lit 7] := by
  cbv

private def missingLast : State [.Lit 7] [.Lit 7, .Lit 8] ∅ where
  planned_mapping := (⊥ : Mapping 1 2).bind 0 0 rfl rfl
  stack := [.Lit 7]
  trace := .Lit _
  mapping := (⊥ : Mapping 1 2).bind 0 0 rfl rfl
  pending_generations := 1

-- Skipping a final prefix must still generate the last target slot.
example :
    (build_bottom_up 0 missingLast
      (by intro i hi; omega) (by decide) (by decide)
      (by intro i; fin_cases i <;> unfold State.is_available <;> decide)).toOption.map
        (fun result => result.1) = some [.Lit 7, .Lit 8] := by
  cbv

-- Every junk target needs a slot, including the last target.
example :
    (build_bottom_up 0 (emptyState [.Wildcard, .Wildcard, .Wildcard])
      (by intro i hi; omega) (by decide) (by decide)
      (by intro i; fin_cases i <;> unfold State.is_available <;> decide)).toOption.map
        (fun result => result.1) = some [.Wildcard, .Wildcard, .Wildcard] := by
  cbv

-- An empty target starts at the end cursor and emits no operation.
example :
    build_bottom_up 0 (emptyState [])
      (by intro i; exact Fin.elim0 i) (by decide) (by decide)
      (by intro i; exact Fin.elim0 i) = .ok ⟨[], .Lit []⟩ := by
  cbv

-- The final target can also require a spill reload.
example :
    (build_bottom_up 0 (emptyState [.Var ⟨37⟩] {⟨37⟩})
      (by intro i hi; omega) (by decide) (by decide)
      (by intro i; fin_cases i; unfold State.is_available; decide)).toOption.map
        (fun result => result.1) = some [.Var ⟨37⟩] := by
  cbv

private abbrev deepSource : Stack := .Var ⟨37⟩ :: List.replicate 16 (.Lit 0)
private abbrev deepTarget : Stack := deepSource ++ [.Var ⟨37⟩]

private def deepState : State deepSource deepTarget ∅ where
  planned_mapping := ⊥
  stack := deepSource
  trace := .Lit _
  mapping := {
    toFun := fun i => some i.castSucc
    invFun := fun j => if h : j.val < 17 then some ⟨j.val, h⟩ else none
    inv a b := by
      have := a.isLt
      split_ifs with h <;> simp_all [Fin.ext_iff, Fin.val_castSucc, eq_comm]
      omega
  }
  pending_generations := 1

-- A blocked copy for the last target must report failure, not an incomplete success.
example :
    build_bottom_up 0 deepState
      (by intro i hi; omega) (by decide) (by decide)
      (by intro i; fin_cases i <;> unfold State.is_available <;> decide) =
        .error (.Blocked 1) := by
  cbv

end BuildBottomUpCursorTests
