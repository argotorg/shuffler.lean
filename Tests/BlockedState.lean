import Batteries.Data.Except
import Shuffler.PermuteAtLowestHeight.Defs
import Shuffler.RemoveSurplus.Defs
import Tests.BuildBottomUpObservations

namespace BlockedStateTests
open Shuffler.Emission Shuffler.Permute BuildBottomUpTestSupport

private abbrev mappingOf (n m : ℕ) (dests : List (Option ℕ)) : Mapping n m :=
  (List.finRange n).foldl (fun mapping src =>
    match dests[src.val]? with
    | some (some d) =>
      if hd : d < m then
        if hs : mapping src = none then
          if hf : mapping.symm ⟨d, hd⟩ = none then mapping.bind src ⟨d, hd⟩ hs hf else mapping
        else mapping
      else mapping
    | _ => mapping) ⊥

private abbrev stateOf (source target : Stack) (dests : List (Option ℕ))
    (pending : ℕ := 0) : State source target ∅ where
  planned_mapping := mappingOf _ _ dests
  stack := source
  trace := .Lit source
  mapping := mappingOf _ _ dests
  pending_generations := pending

private structure Observation where
  blocked : Option Blocked
  stack : Stack
  operations : List Operation
  mapping : List (Option ℕ)
  pending : ℕ
  planned : List (Option ℕ)
  deriving DecidableEq

private def observe (result : Except ShuffleErr (Result source target spills)) : Except ShuffleErr Observation :=
  result.map fun r =>
    ⟨r.blocked, r.state.stack, operations r.state.trace,
      List.ofFn fun i => (r.state.mapping i).map Fin.val, r.state.pending_generations,
      List.ofFn fun i => (r.state.planned_mapping i).map Fin.val⟩

private abbrev values (n : ℕ) : Stack := (List.range n).map (fun i => .Var ⟨i⟩)
private abbrev ids (n : ℕ) : List (Option ℕ) := (List.range n).map some

-- A pop before blocking remains in the returned stack, trace, and mapping.
example : observe (removeSurplus (stateOf (values 19) (values 17)
    (none :: ids 17 ++ [none]))) =
    .ok ⟨some ⟨0, 1⟩, values 18, [.pop], none :: ids 17, 0, none :: ids 17 ++ [none]⟩ := by
  native_decide

private abbrev deepState := stateOf (values 19) (values 19) (ids 19)
private abbrev deepPerm : Permutation deepState.stack := Equiv.swap ⟨18, by decide⟩ ⟨17, by decide⟩ * Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩

-- A reachable swap occurs before a later cycle blocks at depth 17.
example : observe (permute deepState deepPerm) =
    .ok ⟨some ⟨1, 1⟩, (values 19).swap 18 17, [.swap 1],
      ids 19, 0, ids 19⟩ := by native_decide

-- The final permutation in buildBottomUp returns the same partial state.
example : observe (buildBottomUp.loop 0
    (stateOf (values 19) (values 19) ((ids 19).swap 18 17 |>.swap 0 1))) =
    .ok ⟨some ⟨1, 1⟩, (values 19).swap 18 17, [.swap 1],
      ((ids 19).swap 18 17).swap 0 1, 0, (ids 19).swap 18 17 |>.swap 0 1⟩ := by native_decide

-- The lowest-height stage also returns the swaps before blocking.
example : observe (Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight
    (stateOf (values 19) (values 19) ((ids 19).swap 18 17 |>.swap 0 1))) =
    .ok ⟨some ⟨1, 1⟩, (values 19).swap 18 17, [.swap 1],
      ((ids 19).swap 18 17).swap 0 1, 0, (ids 19).swap 18 17 |>.swap 0 1⟩ := by native_decide

private abbrev prefixState : State [.Var ⟨2⟩, .Var ⟨1⟩, .Var ⟨0⟩] (values 3) ∅ where
  planned_mapping := mappingOf _ _ (ids 3)
  stack := values 3
  trace := .Swap 2 (by decide) (by decide) (by decide) (.Lit _)
  mapping := mappingOf _ _ (ids 3)
  pending_generations := 0

-- Success appends to the input trace.
example : observe (permute prefixState (Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩)) =
    .ok ⟨none, (values 3).swap 0 2, [.swap 2, .swap 2],
      ids 3, 0, ids 3⟩ := by native_decide

-- Empty stages complete without a trace operation.
example : observe (permute (stateOf [] [] []) 1) = .ok ⟨none, [], [], [], 0, []⟩ := by decide
example : observe (removeSurplus (stateOf [] [] [])) = .ok ⟨none, [], [], [], 0, []⟩ := by decide
example : observe (Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight (stateOf [] [] [])) =
    .ok ⟨none, [], [], [], 0, []⟩ := by decide

-- DUP blocking preserves both the working state and pending generations.
private abbrev dupState := stateOf (values 17) [.Var ⟨0⟩] (List.replicate 17 none) 1
example : observe (dupState.produce 0) =
    .ok ⟨some ⟨0, 1⟩, values 17, [], List.replicate 17 none, 1, List.replicate 17 none⟩ := by native_decide
example : observe (dupState.generate 0) = observe (dupState.produce 0) := by native_decide

-- SWAP at depth 16 succeeds, and depth 17 blocks without a swap.
example : (observe (permute (stateOf (values 17) (values 17) (ids 17)) (Equiv.swap ⟨0, by decide⟩ ⟨16, by decide⟩))).map
    (fun r => (r.blocked, r.operations)) = .ok (none, [.swap 16]) := by native_decide
example : (observe (permute (stateOf (values 18) (values 18) (ids 18)) (Equiv.swap ⟨0, by decide⟩ ⟨17, by decide⟩))).map
    (fun r => (r.blocked, r.operations)) = .ok (some ⟨0, 1⟩, []) := by native_decide

-- Parking a value returns its swaps and keeps the planned mapping.
example : observe (Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight
    (stateOf [.Var ⟨0⟩, .Var ⟨1⟩] [.Var ⟨1⟩, .Lit 0, .Var ⟨0⟩] [some 2, some 0] 1)) =
    .ok ⟨none, [.Var ⟨1⟩, .Var ⟨0⟩], [.swap 1], [some 2, some 0], 1, [some 2, some 0]⟩ := by
  native_decide

private abbrev retagSource : Stack := (values 19).set 2 (.Var ⟨1⟩)
private abbrev retagDestinations := ((ids 19).swap 0 1).swap 2 3
private abbrev retagState := stateOf retagSource
  (((retagSource.swap 0 1).swap 2 3) ++ [.Lit 0]) retagDestinations 1

-- Copy selection retags a destination, then swaps the copy up before the lower swap blocks.
-- The size check after the loop must allow this blocked stack, which is shorter than the target.
example : observe (buildBottomUp retagState (by constructor <;> native_decide)) =
    .ok ⟨some ⟨0, 2⟩, retagSource.swap 2 18, [.swap 16],
      (retagDestinations.swap 2 1).swap 2 18, 1, retagDestinations⟩ := by native_decide

end BlockedStateTests
