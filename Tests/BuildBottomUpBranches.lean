import Shuffler.BuildBottomUp.Defs

set_option maxRecDepth 16384

namespace BuildBottomUpBranchTests

-- Attaching a proof keeps both success values and errors unchanged.
example (result : Except ShuffleErr ℕ) : result.attach.map Subtype.val = result := by
  cases result <;> rfl

-- The new top is the only unbound target. Generating it must revisit offset zero.
private def newTopState : State [.Lit 10, .Lit 20] [.Lit 20, .Lit 10, .Lit 7] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20]
  trace := .Lit _
  mapping := ((⊥ : Mapping 2 3).bind 0 1 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

private theorem newTopInvariant : LoopInvariant 0 newTopState := by
  intro i hi
  omega

example :
    (build_bottom_up 0 newTopState newTopInvariant
      (by decide) (by decide)
      (by intro i; fin_cases i <;> unfold State.is_available <;> decide)).toOption.map
        (fun result => result.1) = some [.Lit 20, .Lit 10, .Lit 7] := by
  cbv

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

private theorem urgentInvariant : LoopInvariant 2 urgentState := by
  intro i hi
  rcases i with ⟨i, hibound⟩
  change i < 2 at hi
  have hcases : i = 0 ∨ i = 1 := by omega
  rcases hcases with rfl | rfl
  · change urgentState.is_final 0
    decide
  · change urgentState.is_final 1
    decide

example :
    (build_bottom_up 2 urgentState urgentInvariant
      (by decide) (by decide)
      (by intro i; fin_cases i <;> unfold State.is_available <;> decide)).toOption.map
        (fun result => result.1) = some urgentTarget := by
  cbv

private def missingCopyState : State [.Lit 10, .Lit 20] [.Lit 20, .Lit 10, .Var ⟨37⟩] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20]
  trace := .Lit _
  mapping := ((⊥ : Mapping 2 3).bind 0 1 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

-- An unavailable target value cannot satisfy the new input condition.
#check_failure (build_bottom_up 0 missingCopyState
  (by intro i hi; omega)
  (by decide) (by decide)
  (by intro i; fin_cases i <;> unfold State.is_available <;> decide))

private def surplusState : State [.Lit 10, .Lit 20, .Lit 7] [.Lit 20, .Lit 10, .Lit 7] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20, .Lit 7]
  trace := .Lit _
  mapping := ((⊥ : Mapping 3 3).bind 0 1 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

-- A stack at target height cannot reserve room for another generation.
#check_failure (build_bottom_up 0 surplusState
  (by intro i hi; omega)
  (by decide) (by decide)
  (by intro i; fin_cases i <;> unfold State.is_available <;> decide))

/-- info: 'State.generate_effects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.generate_effects

/-- info: 'State.generate_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.generate_preserves

end BuildBottomUpBranchTests
