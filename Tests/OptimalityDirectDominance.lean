import Shuffler.Optimality.DirectDominance.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityDirectDominance

open Shuffler.Optimality

private def zero : Value := .Lit 0
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)
private def sample : Trace ∅ [] [zero, zero] :=
  .Dup 1 (by decide) (by decide) (by decide) (.Push zero (by decide) (.Lit []))

#guard flatten (DirectDominance.normalize costs .gasOnly sample) = [.push zero, .push zero]
#guard traceCost costs sample = ⟨5, 2⟩
#guard traceCost costs (DirectDominance.normalize costs .gasOnly sample) = ⟨4, 2⟩
#guard DirectDominance.statePath (DirectDominance.normalize costs .gasOnly sample) =
  DirectDominance.statePath sample

private def wideCosts : PrimitiveCosts := PrimitiveCosts.evm
  (fun _ => .push ⟨31, by decide⟩) (fun _ => .push ⟨31, by decide⟩)

-- A tie in gas can increase byte cost. The theorem uses the chosen weights.
#guard flatten (DirectDominance.normalize wideCosts .gasOnly sample) = [.push zero, .push zero]
#guard (traceCost wideCosts sample).bytes = 34
#guard (traceCost wideCosts (DirectDominance.normalize wideCosts .gasOnly sample)).bytes = 66
#guard flatten (DirectDominance.normalize wideCosts .bytesOnly sample) = [.push zero, .dup 1]

private def id : VarId := ⟨42⟩
private def value : Value := .Var id
private def spilled : SpillSet := {id}
private def loadCosts : PrimitiveCosts := { costs with load := fun _ => ⟨1, 0⟩ }
private def loadSample : Trace spilled [value] [value, value] :=
  .Dup 1 (by decide) (by decide) (by decide) (.Lit [value])
private def unavailable : Trace ∅ [value] [value, value] :=
  .Dup 1 (by decide) (by decide) (by decide) (.Lit [value])
private def label : Trace ∅ [.FunctionReturnLabel] [.FunctionReturnLabel, .FunctionReturnLabel] :=
  .Dup 1 (by decide) (by decide) (by decide) (.Lit [.FunctionReturnLabel])
private def wildcard : Trace ∅ [.Wildcard] [.Wildcard, .Wildcard] :=
  .Dup 1 (by decide) (by decide) (by decide) (.Lit [.Wildcard])

#guard flatten (DirectDominance.normalize loadCosts .gasOnly loadSample) = [.load id]
#guard flatten (DirectDominance.normalize loadCosts .gasOnly unavailable) = [.dup 1]
#guard flatten (DirectDominance.normalize costs .gasOnly label) = [.dup 1]
#guard flatten (DirectDominance.normalize costs .gasOnly wildcard) = [.push .Wildcard]
#guard ¬DirectDominance.CheapDirect costs .gasOnly ∅ value
#guard ¬DirectDominance.CheapDirect costs .gasOnly ∅ .FunctionReturnLabel

private def deepSource : Stack := List.replicate 17 zero
private def deepDup : Trace ∅ deepSource (deepSource ++ [zero]) :=
  .Dup 16 (by decide) (by decide) (by decide) (.Lit deepSource)
private def withPop : Trace ∅ [] [zero] := .Pop (by decide) sample

#guard flatten (DirectDominance.normalize costs .gasOnly deepDup) = [.push zero]
#guard flatten (DirectDominance.normalize costs .gasOnly withPop) = [.push zero, .push zero, .pop]
#guard flatten (DirectDominance.normalize costs .gasOnly (Trace.Lit ([] : Stack) (spills := ∅))) = []

example : DirectDominance.statePath (DirectDominance.normalize costs .gasOnly deepDup) =
    DirectDominance.statePath deepDup := DirectDominance.normalize_statePath costs .gasOnly deepDup

example : Lineage.dupCount zero (DirectDominance.normalize costs .gasOnly sample) = 0 :=
  DirectDominance.normalize_dupCount_zero costs .gasOnly sample zero (by decide)

example : (traceCost costs (DirectDominance.normalize costs .gasOnly sample)).score .gasOnly ≤
    (traceCost costs sample).score .gasOnly := DirectDominance.normalize_score_le costs .gasOnly sample

example : ¬(DirectDominance.normalize costs .gasOnly withPop).noPop := by
  rw [DirectDominance.normalize_noPop]
  intro h
  exact h

end Tests.OptimalityDirectDominance
