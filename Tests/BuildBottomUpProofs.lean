import Shuffler

open Shuffler.BuildBottomUp

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`Experiments).isPrefixOf name then
      throwError "production imports experiment module {name}"

set_option maxRecDepth 16384

namespace BuildBottomUpProofTests

-- The assertion proof is checked without sorryAx.
/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_noAssertion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_noAssertion

/-- info: 'Shuffler.BuildBottomUp.buildBottomUp_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms buildBottomUp_terminates

-- Equal values at the current offset exchange destinations without a swap.
private def equalCurrentState : State [.Lit 10, .Lit 10] [.Lit 10, .Lit 7, .Lit 10] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 10]
  trace := .Lit _
  mapping := ((⊥ : Mapping 2 3).bind 0 2 rfl rfl).bind 1 0 (by decide) (by decide)
  pending_generations := 1

example : Invariant 0 equalCurrentState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example :
    (buildBottomUp equalCurrentState).toOption.map
        (fun result => (result.1, result.2.swapCount)) =
      some ([.Lit 10, .Lit 7, .Lit 10], 1) := by
  native_decide

-- The search selects an equal, movable copy at the top and stops there.
private def equalCandidateState :
    State [.Lit 10, .Lit 20, .Lit 20] [.Lit 20, .Lit 7, .Lit 10, .Lit 20] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20, .Lit 20]
  trace := .Lit _
  mapping := (((⊥ : Mapping 3 4).bind 0 2 rfl rfl).bind 1 0 (by decide) (by decide)).bind
    2 3 (by decide) (by decide)
  pending_generations := 1

example : Invariant 0 equalCandidateState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example :
    (buildBottomUp equalCandidateState).toOption.map
        (fun result => (result.1, result.2.swapCount)) =
      some ([.Lit 20, .Lit 7, .Lit 10, .Lit 20], 2) := by
  native_decide

-- A final equal copy must be skipped by the search.
private def finalCandidateState :
    State [.Lit 10, .Lit 20, .Lit 20] [.Lit 20, .Lit 7, .Lit 20, .Lit 10] ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20, .Lit 20]
  trace := .Lit _
  mapping := (((⊥ : Mapping 3 4).bind 0 3 rfl rfl).bind 1 0 (by decide) (by decide)).bind
    2 2 (by decide) (by decide)
  pending_generations := 1

example : Invariant 0 finalCandidateState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example :
    (buildBottomUp finalCandidateState).toOption.map
        (fun result => (result.1, result.2.swapCount)) =
      some ([.Lit 20, .Lit 7, .Lit 20, .Lit 10], 4) := by
  native_decide

private def retainAll (n : ℕ) : Mapping n (n + 1) where
  toFun := fun i => some i.castSucc
  invFun := fun j => if h : j.val < n then some ⟨j.val, h⟩ else none
  inv a b := by
    have := a.isLt
    split_ifs with h <;> simp_all [Fin.ext_iff, Fin.val_castSucc, eq_comm]
    omega

-- At offset one, the bound copy is one slot beyond SWAP reach.
private def blockedSwapUpState :
    State ([.Lit 10, .Lit 20] ++ List.replicate 17 (.Lit 30))
      ([.Lit 20, .Lit 10] ++ List.replicate 17 (.Lit 30) ++ [.Lit 7]) ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10, .Lit 20] ++ List.replicate 17 (.Lit 30)
  trace := .Lit _
  mapping := by simpa using (retainAll 19).swapDestinations 0 1
  pending_generations := 1

example : Invariant 0 blockedSwapUpState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example : (buildBottomUp blockedSwapUpState).map (fun result => result.1) =
    .error (.blocked 1) := by
  native_decide

-- The bound copy is on top, but offset zero is one slot beyond SWAP reach.
private def blockedSwapDownState :
    State ([.Lit 10] ++ List.replicate 16 (.Lit 30) ++ [.Lit 20])
      ([.Lit 20] ++ List.replicate 16 (.Lit 30) ++ [.Lit 10, .Lit 7]) ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10] ++ List.replicate 16 (.Lit 30) ++ [.Lit 20]
  trace := .Lit _
  mapping := by simpa using (retainAll 18).swapDestinations 0 17
  pending_generations := 1

example : Invariant 0 blockedSwapDownState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example : (buildBottomUp blockedSwapDownState).map (fun result => result.1) =
    .error (.blocked 1) := by
  native_decide

-- Generation can leave its destination on top when the final swap is out of reach.
private def blockedGeneratedState :
    State ([.Lit 10] ++ List.replicate 16 (.Lit 30))
      ([.Lit 7] ++ List.replicate 16 (.Lit 30) ++ [.Lit 10]) ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10] ++ List.replicate 16 (.Lit 30)
  trace := .Lit _
  mapping := by simpa using (Mapping.swapDestinations (retainAll 17).symm 0 17).symm
  pending_generations := 1

example : Invariant 0 blockedGeneratedState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example : (buildBottomUp blockedGeneratedState).map (fun result => result.1) =
    .error (.blocked 1) := by
  native_decide

-- At the limit, SWAP16 succeeds and the last target slot is generated.
private def swapLimitState :
    State ([.Lit 10] ++ List.replicate 15 (.Lit 30) ++ [.Lit 20])
      ([.Lit 20] ++ List.replicate 15 (.Lit 30) ++ [.Lit 10, .Lit 7]) ∅ where
  planned_mapping := ⊥
  stack := [.Lit 10] ++ List.replicate 15 (.Lit 30) ++ [.Lit 20]
  trace := .Lit _
  mapping := by simpa using (retainAll 17).swapDestinations 0 16
  pending_generations := 1

example : Invariant 0 swapLimitState :=
  ⟨(by intro i hi; omega), by decide, by decide,
    by intro i; fin_cases i <;> unfold State.isAvailable <;> decide⟩

example :
    (buildBottomUp swapLimitState).toOption.map
        (fun result => (result.1, result.2.swapCount)) =
      some ([.Lit 20] ++ List.replicate 15 (.Lit 30) ++ [.Lit 10, .Lit 7], 1) := by
  native_decide

end BuildBottomUpProofTests
