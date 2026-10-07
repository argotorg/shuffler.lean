import Shuffler.Optimality.ForcedIntroduction.Cost
import Shuffler.Optimality.GroupEntry.Theorems
import Shuffler.Optimality.Replay

namespace Tests.OptimalityForcedIntroduction

open Shuffler.Optimality Shuffler.Placement

set_option maxRecDepth 8192

private def a : Value := .Var ⟨42⟩
private def wide : Value := .Lit (2 ^ 248)
private def zero : Value := .Lit 0
private def spills : SpillSet := {⟨42⟩}
private def costs : PrimitiveCosts := PrimitiveCosts.evm
  (fun value => if value = zero then .push0 else .push ⟨31, by decide⟩)
  (fun _ => .push ⟨1, by decide⟩)
private def source (value : Value) : Stack := List.replicate 16 zero ++ [value]
private def target (value : Value) : Stack := value :: List.replicate 16 zero ++ [value]
private def built := (replayExact spills (source a) (target a) {a}
  [.swap 16, .load ⟨42⟩]).get (by decide)
private def wideBuilt := (replayExact ∅ (source wide) (target wide) {wide}
  [.swap 16, .push wide]).get (by decide)

-- The only initial a is needed for the boundary. No seed remains for DUP.
#guard ForcedIntroduction.Required a (source a) (target a) {a}
#guard ForcedIntroduction.Required wide (source wide) (target wide) {wide}
#guard ForcedIntroduction.bound costs Weights.bytesOnly spills (source a) (target a) {a} = 3
#guard baseline costs Weights.bytesOnly spills (source a) {a} = 1
#guard (traceCost costs built.trace).bytes = 5
#guard Lineage.directCount a built.trace = 1
#guard GroupEntry.requiredSwaps (source a) (target a) {a} = 1
#guard ForcedIntroduction.bound costs Weights.bytesOnly ∅ (source wide) (target wide) {wide} = 32
#guard baseline costs Weights.bytesOnly ∅ (source wide) {wide} = 1
#guard (traceCost costs wideBuilt.trace).bytes = 34

-- A second initial copy leaves a readable seed after the boundary is fixed.
#guard ¬ForcedIntroduction.Required a (a :: List.replicate 15 zero ++ [a])
  (a :: List.replicate 15 zero ++ [a, a]) {a}
-- At height16, the first birth does not freeze the bottom position yet.
#guard ¬ForcedIntroduction.Required a (List.replicate 15 zero ++ [a])
  (a :: List.replicate 15 zero ++ [a]) {a}
-- A different boundary value leaves the sole seed available.
#guard ¬ForcedIntroduction.Required a (source a) (source a ++ [a]) {a}
-- A value outside the initial movable window also needs direct introduction.
#guard ForcedIntroduction.Required a (a :: List.replicate 17 zero)
  (a :: List.replicate 17 zero ++ [a]) {a}
#guard ForcedIntroduction.Required a [] [a] {a}
#guard ForcedIntroduction.bound costs Weights.bytesOnly spills [] [a] {a} = 0
#guard ¬ForcedIntroduction.Required a [a] [a] 0
#guard ¬ForcedIntroduction.Required zero [zero] [zero, zero] {zero}

example (trace : Trace spills (source a) (target a)) (he : Eligible {a} trace) :
    0 < Lineage.directCount a trace :=
  ForcedIntroduction.Required.directCount_pos a trace he.1 (he.2.symm ▸ (by decide))

example (trace : Trace ∅ (source wide) (target wide)) (he : Eligible {wide} trace) :
    0 < Lineage.directCount wide trace :=
  ForcedIntroduction.Required.directCount_pos wide trace he.1 (he.2.symm ▸ (by decide))

example (trace : Trace spills (source a) (target a)) (he : Eligible {a} trace) :
    5 ≤ (traceCost costs trace).bytes := by
  have h := ForcedIntroduction.baseline_add_swapFloor_add_bound_le_score
    costs Weights.bytesOnly trace he _ (GroupEntry.requiredSwaps_le_swapCount trace he)
  have hc : baseline costs Weights.bytesOnly spills (source a) {a} +
      costs.swap.score Weights.bytesOnly * GroupEntry.requiredSwaps (source a) (target a) {a} +
        ForcedIntroduction.bound costs Weights.bytesOnly spills (source a) (target a) {a} = 5 := by decide
  rw [hc] at h
  simpa only [Cost.score_bytesOnly] using h

example (trace : Trace ∅ (source wide) (target wide)) (he : Eligible {wide} trace) :
    34 ≤ (traceCost costs trace).bytes := by
  have h := ForcedIntroduction.baseline_add_swapFloor_add_bound_le_score
    costs Weights.bytesOnly trace he _ (GroupEntry.requiredSwaps_le_swapCount trace he)
  have hc : baseline costs Weights.bytesOnly ∅ (source wide) {wide} +
      costs.swap.score Weights.bytesOnly * GroupEntry.requiredSwaps (source wide) (target wide) {wide} +
        ForcedIntroduction.bound costs Weights.bytesOnly ∅ (source wide) (target wide) {wide} = 34 := by decide
  rw [hc] at h
  simpa only [Cost.score_bytesOnly] using h

example (source target : Stack) (trace : Trace spills source target) (he : Eligible missing trace) :
    baseline costs weights spills source missing + costs.swap.score weights * trace.swapCount +
      ForcedIntroduction.bound costs weights spills source target missing ≤
        (traceCost costs trace).score weights :=
  ForcedIntroduction.baseline_add_swapCost_add_bound_le_score costs weights trace he

end Tests.OptimalityForcedIntroduction
