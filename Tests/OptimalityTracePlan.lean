import Shuffler.Optimality.BirthPlacement.TracePlan.Build
import Shuffler.Optimality.Replay

namespace Tests.OptimalityTracePlan

open Shuffler.Optimality Shuffler.Optimality.BirthPlacement

private def a : Value := .Lit 0
private def b : Value := .Lit 1
private def c : Value := .Lit 2

private def check (spills : SpillSet) (ops : List Op) : Bool :=
  match replay spills [] ops with
  | none => false
  | some result =>
    let plan := tracePlan result.built.trace result.built.noPop
    decide (birthWord result.target plan.assignment = SwapRuns.births result.built.trace) &&
    decide (plan.events = traceEvents result.built.trace) &&
    decide (plan.assignment.support.card ≤ 2 * result.built.trace.swapCount) &&
    ((replay spills [] (flatten (realize plan).built.trace)).map (·.target) == some result.target)

#guard check ∅ []
#guard check ∅ [.push a, .push b, .swap 1]
#guard check ∅ [.push a, .push a, .swap 1]
#guard check ∅ [.push a, .push b, .push c, .swap 2, .swap 1, .dup 3, .swap 2]
#guard check {⟨42⟩} [.load ⟨42⟩, .push b, .swap 1, .dup 1]
#guard check ∅ [.push .Wildcard, .push a, .swap 1, .dup 2]
#guard check ∅ ([.push a] ++ List.replicate 15 (.push b) ++ [.dup 16, .swap 16])
#guard check ∅ ([.push a] ++ List.replicate 17 (.push b) ++ [.swap 16, .dup 16])

-- Token identities remain distinct even when equal values are exchanged.
#guard (replay ∅ [] [.push a, .push a, .swap 1]).map
  (fun result => (traceAssignment result.built.trace result.built.noPop).support.card) = some 2

-- Extraction also handles initial tokens. The realizer theorem remains scoped
-- to the empty source.
#guard (replay ∅ [a, b, c] [.swap 2, .swap 1, .push a]).map
  (fun result => birthWord result.target (traceAssignment result.built.trace result.built.noPop)) =
    some [a, b, c, a]

#guard ¬check ∅ [.dup 1]
#guard ¬check ∅ (List.replicate 17 (.push a) ++ [.dup 17])
#guard ¬check ∅ (List.replicate 18 (.push a) ++ [.swap 17])
#guard ¬check ∅ [.push a, .pop]

example (trace : Trace spills [] target) (hpop : trace.noPop) :
    (tracePlan trace hpop).events = traceEvents trace := tracePlan_events trace hpop

example (trace : Trace spills [] target) (hpop : trace.noPop) :
    (tracePlan trace hpop).assignment.support.card ≤ 2 * trace.swapCount := tracePlan_moved_le trace hpop

end Tests.OptimalityTracePlan
