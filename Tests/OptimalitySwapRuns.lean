import Shuffler.Optimality.SwapRuns.Theorems
import Shuffler.Optimality.Schedule.Original

namespace Tests.OptimalitySwapRuns

open Shuffler.Optimality

private def a : Value := .Lit 1
private def b : Value := .Lit 2
private def pair : Stack := [a, b]
private def roundTrip : Trace ∅ pair pair :=
  .Swap 1 (by decide) (by decide) (by decide)
    (.Swap 1 (by decide) (by decide) (by decide) (.Lit pair))

#guard roundTrip.swapCount = 2
#guard (SwapRuns.normalize roundTrip).swapCount = 0

private def doubled : Trace ∅ pair (pair ++ [b]) :=
  .Dup 1 (by decide) (by decide) (by decide) roundTrip
private def mixed : Trace ∅ pair (pair ++ [b]) :=
  .Swap 2 (by decide) (by decide) (by decide)
    (.Swap 2 (by decide) (by decide) (by decide) doubled)

#guard mixed.swapCount = 4
#guard (SwapRuns.normalize mixed).swapCount = 0
#guard flatten (SwapRuns.normalize mixed) = [.dup 1]
#guard SwapRuns.births (SwapRuns.normalize mixed) = [b]

private def withPush : Trace ∅ pair (pair ++ [a]) := .Push a (by decide) roundTrip
private def withPop : Trace ∅ pair [a] := .Pop (by decide) roundTrip
private def spill : SpillSet := {⟨42⟩}
private def withLoad : Trace spill pair (pair ++ [.Var ⟨42⟩]) :=
  .Load ⟨42⟩ (by decide)
    (.Swap 1 (by decide) (by decide) (by decide)
      (.Swap 1 (by decide) (by decide) (by decide) (.Lit pair)))

#guard flatten (SwapRuns.normalize withPush) = [.push a]
#guard flatten (SwapRuns.normalize withPop) = [.pop]
#guard flatten (SwapRuns.normalize withLoad) = [.load ⟨42⟩]
#guard flatten (SwapRuns.normalize (Trace.Lit ([] : Stack) (spills := ∅))) = []

private def equalSwap : Trace ∅ [a, a] [a, a] :=
  .Swap 1 (by decide) (by decide) (by decide) (.Lit [a, a])
private def oneSwap : Trace ∅ pair [b, a] :=
  .Swap 1 (by decide) (by decide) (by decide) (.Lit pair)

#guard (SwapRuns.normalize equalSwap).swapCount = 0
#guard (SwapRuns.normalize oneSwap).swapCount = 1

-- A long stack fixes its lower prefix. The run uses the SWAP16 boundary.
private def longSource : Stack := List.replicate 19 a ++ [b]
private def longRoundTrip : Trace ∅ longSource longSource :=
  .Swap 16 (by decide) (by decide) (by decide)
    (.Swap 16 (by decide) (by decide) (by decide) (.Lit longSource))

#guard (SwapRuns.normalize longRoundTrip).swapCount = 0

example : ¬(SwapRuns.normalize withPop).noPop := by
  rw [SwapRuns.normalize_noPop]
  exact id

example : (SwapRuns.normalize mixed).additions = mixed.additions :=
  SwapRuns.normalize_additions mixed

example (costs : PrimitiveCosts) :
    (traceCost costs (SwapRuns.normalize mixed)).AtMost (traceCost costs mixed) :=
  SwapRuns.normalize_cost_le costs mixed

example (other : Trace ∅ pair pair) (he : Eligible 0 other) :
    (SwapRuns.normalize roundTrip).swapCount ≤ other.swapCount :=
  SwapRuns.normalize_noGrowth_min_swaps roundTrip other ⟨by trivial, rfl⟩ he

-- The original BBU leaves a twenty-SWAP suffix on this fixture. Exact
-- value placement replaces that suffix by one SWAP15.
private def old : Value := .Lit 0
private def va : Value := .Var ⟨42⟩
private def vb : Value := .Var ⟨43⟩
private def source : Stack := List.replicate 15 old
private def target : Stack := [va] ++ List.replicate 12 vb ++ [va] ++ source
private def missing : Multiset Value := {va, va} + Multiset.replicate 12 vb
private def spills : SpillSet := {⟨42⟩, ⟨43⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.cppEstimate
  (fun _ => .push0) (fun _ => .push ⟨31, by decide⟩)
private def original := Schedule.originalCandidate spills source target missing

#guard original.map (fun built => traceCost costs built.trace) = some ⟨150, 146⟩
#guard original.map (fun built => traceCost costs (SwapRuns.normalize built.trace)) = some ⟨93, 127⟩
#guard original.map (fun built => SwapRuns.withoutSwaps (SwapRuns.normalize built.trace)) =
  original.map (fun built => SwapRuns.withoutSwaps built.trace)
#guard original.map (fun built => SwapRuns.births (SwapRuns.normalize built.trace)) =
  original.map (fun built => SwapRuns.births built.trace)
#guard original.map (fun built => flatten (SwapRuns.normalize (SwapRuns.normalize built.trace))) =
  original.map (fun built => flatten (SwapRuns.normalize built.trace))

end Tests.OptimalitySwapRuns
